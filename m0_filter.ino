/*
--------------------------------------------------------------------------
Copyright 2020, 2021 Magnus Öberg

Permission to use, copy, modify, and/or distribute this software for
any purpose with or without fee is hereby granted, provided that the
above copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
--------------------------------------------------------------------------

Trinket M0 parameterized filter
===============================

Written by SA5MOG Magnus Öberg (Moggen)

The main idea of this program is to implement a parameterized bandpass
filter using the Adafruit Trinket M0 module.

The ATSAMD21E18 CPU does not have hardware support for floating point.
This means that code using floating point will be (very) slow on this
platform. Fixed point integer arithmetic needs to be used to get
any reasonable calculation performance.

The program is structured into a setup section (the standard Arduino
"setup()" function) and two main loops running at the same time.
One of the loops is running as a timer controlled interrupt service
routine, and the other loop runs continously in the background (the
standard Arduino "loop()")

The timer loop is responsible for sampling the input, performing digital
filtering and outputting the resulting signal again.
The performance in this loop is critical, and the M0 CPU spends most of
the time in this interrupt routine. Floating point code can not be used.
The timer loop is actually sampling twice per loop. Once for the input
sample, and once for one of the potentiometers (in a round-robin scheme)

The background loop is continously running generation of new filter
attributes based on the potentiometer samplings made by the timer
loop. This loop is more relaxed, and a few float operations will be
acceptable. But the response when adjusting the potentiometers will be 
sluggish if this loop is too slow, so some fixed point math is needed
here as well.

The sample rate was set to 20 kHz. This is perhaps suprisingly high
as this filter typically operates with bandwidth up to 4 kHz.
This was chosen to ease the complexity on a analog input filter.
It only needs to suppress noise at 16 kHz and up.

Pinout assumed on the Trinket MO:

Pin 0 / A2 / (PA08) - Upper frequency potentiometer input
Pin 1 / A0 / (PA02) - Analog output
Pin 2 / A1 / (PA09) - Analog input
Pin 3 / A3 / (PA07) - Gain potentiometer input
Pin 4 / A4 / (PA06) - Lower frequency potentiometer input

The range for all pins are GND to VDD (3.3V). Analog input protection
diodes are highly recommended. Potentiomenters are typically linear 10kOhm
*/

// Uncomment to enable debug output on the virtual USB serial port
//#define DEBUG 1

#include <Adafruit_DotStar.h>
// Init DotStar module
Adafruit_DotStar strip = Adafruit_DotStar(1, 7, 8, DOTSTAR_BGR);

// Useful macros for syncing
#define GCLK_SYNC() while(GCLK->STATUS.bit.SYNCBUSY){}
#define TC5_SYNC() while(TC5->COUNT16.STATUS.bit.SYNCBUSY){}
#define ADC_SYNC() while(ADC->STATUS.bit.SYNCBUSY){}

// Main sample rate
#define sampleRate 20000

// The FIR length, optimized for the performance of the Trinket M0
#define FIR_LEN 215

// The table lengths are about half size. The FIR filters used in
// this program are _always_ symmetrical so we only need one half.
#define FIR_LEN_TABLE ((FIR_LEN>>1)+1)

// The main sample buffer used for filtering.
// It is actually two adjacent copies of a circular buffer.
// This avoids wrapping checks in the inner loop.
// The cost is an extra buffer write per sample and double amount of RAM
int32_t samples[FIR_LEN*2];
int next_idx;

// Double-buffered FIR tap arrays
int32_t fir1[FIR_LEN_TABLE], fir2[FIR_LEN_TABLE];

// Communication between the timer loop and the background loop is done
// through global data, and these are defined as volatile to avoid
// problems with compiler optimizations

// The current live buffer. Reads and writes to a volatile pointer are
// assumed to be atomic!
volatile int32_t *fir = fir1;

// Main working variables, current sample and current output
volatile uint32_t s, o;

// Gain
volatile uint32_t gain = 0;

// Potentiometer sampling
volatile uint32_t p_gain = 0, p_f1 = 0, p_f2 = 0;

// Wait loop counters for ADC
volatile uint32_t cnt, cnt2;

// Signal level overdrive detection
volatile uint32_t output_error_ticks = 65000;
volatile uint32_t output_warning_ticks = 65000;
#define OUTPUT_ERROR_LEVEL_HIGH 896
#define OUTPUT_ERROR_LEVEL_LOW 128
#define OUTPUT_WARNING_LEVEL_HIGH 768
#define OUTPUT_WARNING_LEVEL_LOW 256

// Some timing for debug messages
#ifdef DEBUG
  volatile unsigned long timing = 0;
  volatile unsigned long lastt = 0;
#endif

// Hamming window function using floating points.
float hamming_float(float x) {
  return 0.53836f - 0.46164f * cosf(2.0f * M_PI * x / (FIR_LEN-1));
}

// Fixed point LUT for the Hamming window.
int16_t hamming_lut_S14[FIR_LEN_TABLE];

// Lookup macro
#define hamming_S14(i) (hamming_lut_S14[i])

// Init of LUT (called once at setup)
void prepare_hamming() {
  for(int i=0; i<FIR_LEN_TABLE; i++)
    hamming_lut_S14[i] = (int16_t)(hamming_float((float)i) * (float)(1<<14));
}

// Sinus with period=1.0 and divided by Pi, float version
float sinP1dPi_float(float x) {
  return sinf(x*2.0f*M_PI) / M_PI;
}

// Fixed point LUT. 512 entries for one period
int16_t sinP1dPi_lut_S14[512];

// Lookup function
int16_t sinP1dPi_S14(int32_t x_S14) {
  return sinP1dPi_lut_S14[(x_S14 & ((1<<14)-1)) >> 5];
}

// Init of LUT
void prepare_sinus() {
  for(int x = 0; x < 512; x++) {
    sinP1dPi_lut_S14[x] = (int16_t)(sinP1dPi_float((float)x / 512.0f) * (float)(1<<14));
  }
}

/*
  The main FIR filter generation code.

  The filter is directly generated from the two corner frequencies
  defining the passband filter using SINC functions. There are lots
  of methods of generating passband filters but this is a quite
  simple one conceptually and has the benefit of zero phase distortion
  (except for the group delay of FIR size / 2).

  Using the output of the SINC function as the taps in a FIR filter
  gives a perfect low pass filter (assuming infinite number of taps).
  Subtracting another SINC output from this makes a perfect band pass
  or band stop filter.

  But we need to limit the amount of FIR taps obviously. We can simply
  just cut off the ends to get the most important taps around the middle
  (time=0). This will introduce artifacts in the spectrum, so called
  side lobes. These can be suppressed with window functions like the
  Hamming window.

  The generated filter will of couse not be ideal and have transition
  regions at the corner frequencies and some remaining side lobe
  interference even if a window function is used. But it'll have to do.

  This kind of FIR filter always comes with a fixed added delay of
  half the number of taps in the filter.

  In our case 215 taps -> 107 samples delay @20 kHz = 5.35 ms delay.
  There will also be an additional delay of 2 samples because of
  buffering in the timer loop of input and output values.

  So the total delay should be around 109 samples = 5.45 ms

  For some deep dive into the maths, see:
  https://www.dsprelated.com/freebooks/sasp/FIR_Digital_Filter_Design.html

  The SINC filter (also called brick wall filter) is explained here:
  https://en.wikipedia.org/wiki/Sinc_filter

  I've been using definitions and formulas from the Wikipedia article.
  The lower start frequency is denoted as B and it is the digital
  normalized frequency. This is the same as the frequency/sample rate.
  B2 is the normalized upper stop frequency.

  The normalized SINC function is defined as
  SINC(x) = SIN(Pi * x) / (Pi * x)
  x=0 is a special case and SINC(0) is defined as 1

  The impulse response (FIR taps) for the ideal low pass filter with
  corner frequency B is:
  h(t) = 2*B * SINC(2*B*t)

  This is the original non-optimized generation code:

    float sinc(float x) {
      if(x > -0.00001 && x < 0.00001)
        return 1.0f;  // 1.0 by definition
      return sinf(M_PI*x) / (M_PI*x);
    }

    void prepare_fir(int16_t *fir, int freq1, int freq2) {
      float B = (float)freq1 / sampleRate;
      float B2 = (float)freq2 / sampleRate;
      for(int i=0; i < FIR_LEN; i++) {
        float r = 2.0f * B2 * sinc((i - (FIR_LEN >> 1)) * 2.0f * B2);
        r -= 2.0f * B * sinc((i - (FIR_LEN >> 1)) * 2.0f * B);
        r *= hamming_float(i);
        r *= 1 << 16;
        fir[i] = (int16_t)r;
      }
    }

  Below is the same calculation but heavily optimized.
  The final FIR tap data is in fixed point integer format,
  upshifted 16 bits. Only half of the taps are generated and
  used as the tap values are symmetric around 0 (the midpoint).
*/
void prepare_fir(int32_t *fir, float freq1, float freq2) {
  int32_t B_S14 = (int32_t)(freq1 * (float)(1 << 14) / sampleRate);
  int32_t B2_S14 = (int32_t)(freq2 * (float)(1 << 14) / sampleRate);

  int32_t B_cur = -(FIR_LEN >> 1);

  int32_t B_cur2_S14 = -(FIR_LEN >> 1) * B_S14;
  int32_t B2_cur2_S14 = -(FIR_LEN >> 1) * B2_S14;

  int32_t r_S14, r_S16;
  int i;
  for(i=0; i<FIR_LEN_TABLE-1; i++) {
    r_S14 = -sinP1dPi_S14(B_cur2_S14) + sinP1dPi_S14(B2_cur2_S14);
    r_S16 = (r_S14 * hamming_S14(i) / B_cur) >> 12;
    fir[i] = r_S16;
    B_cur += 1;
    B_cur2_S14 += B_S14;
    B2_cur2_S14 += B2_S14;
  }
  // Last value, B_cur is 0 so we cant divide by it.
  // This is the SINC(0) case and it is 1.0 by definition
  r_S14 = (-B_S14 + B2_S14 ) << 1;   // (-B + B2) * 2
  r_S16 = (r_S14 * hamming_S14(i)) >> 12;
  fir[i] = r_S16;
}

// Init routine, run once after boot
void setup() {

  // Start by initialize the DotStar RGB and switch it off.
  // The DotStar LED is causing a small interference on the ADC
  // sampling, so we want to keep it off under normal operating
  // conditions.
  strip.begin();
  strip.setBrightness(50);  // Adjust here if it is to bright or dull
  strip.setPixelColor(0, 0, 0, 0);  // Black = off
  strip.show();

  // Init buffers
  for(int i=0; i<FIR_LEN; i++) {
    samples[i] = 0;
    samples[i+FIR_LEN] = 0;
    fir1[i] = 0;
    fir2[i] = 0;
  }
  // Prepare lookup tables
  prepare_hamming();
  prepare_sinus();

  // Set up an initial FIR filter that blocks everything
  prepare_fir(fir1, 0.0f, 0.0f);
  next_idx = 0;

  // We use 10 bits for the DAC and ADC hardware
  analogWriteResolution(10);
  analogReadResolution(10);

  // Dummy reads and writes to get all pin muxes and modes correctly set (by the Arduino libraries)
  analogRead(A1);         // A1 / Pin 2 / PA09 as analog input of signal
  analogRead(A2);         // A2 / Pin 0 / PA08 analog input, potentiometer 1, Frequency 2, top frequency
  analogRead(A3);         // A3 / Pin 3 / PA07 analog input, potentiometer 2, Gain (Volume)
  analogRead(A4);         // A4 / Pin 4 / PA06 analog input, potentiometer 3, Frequency 1, bottom frequency
  analogWrite(A0, 512);   // A0 / Pin 1 / PA02 as analog output of signal

  // Switch off pin 13 LED
  pinMode(13, OUTPUT);
  digitalWrite(13, LOW);
  
  // This part overrides ADC parameters manually. The Arduino environment has nice
  // support for AD conversion, but it contains lots of checking code to make
  // sure that pin modes are set etc. every time we sample. We do not need that
  // and we also want to do some precise tuning.
  ADC_SYNC();
  ADC->CTRLB.reg = ADC_CTRLB_PRESCALER_DIV32 |    // Divide the 48 MHz system clock by 32
                   ADC_CTRLB_RESSEL_10BIT;        // 10 bits resolution

  // Set sampling time length. This will determine the input impedance.
  // See this excellent calculator (and her other posts):
  // https://blog.thea.codes/getting-the-most-out-of-the-samd21-adc/
  
  // Length 14 gives an impedance of about 155 kOhm and this will work
  // great with 10 kOhm potentiometers.

  // Length 14 also results in a total conversion time of 9.33 µs. This
  // is fine as we have a time budget of 50 µs in the timer loop and
  // we need to sample twice.
  ADC->SAMPCTRL.reg = 14;
  ADC_SYNC();
  ADC->CTRLA.bit.ENABLE = 0x01;             // Enable ADC
  ADC_SYNC();
  ADC->INTFLAG.reg = ADC_INTFLAG_RESRDY;    // Clear the Data Ready flag
  ADC_SYNC();

  // Prepare to use A1 for sampling
  ADC->INPUTCTRL.bit.MUXPOS = g_APinDescription[A1].ulADCChannelNumber;
  ADC_SYNC();

  // Prepare hardware timer TC5 to trigger at the sample rate
  // Route GCLK0 (48MHz) to timers TC4 and TC5
  GCLK->CLKCTRL.reg = (uint16_t) (GCLK_CLKCTRL_CLKEN | GCLK_CLKCTRL_GEN_GCLK0 | GCLK_CLKCTRL_ID(GCM_TC4_TC5)) ;
  GCLK_SYNC();

  // Reset TC5 
  TC5->COUNT16.CTRLA.reg = TC_CTRLA_SWRST;
  TC5_SYNC();

  // Wait until reset is complete
  while(TC5->COUNT16.CTRLA.bit.SWRST){};

  // Configure TC5
  TC5->COUNT16.CTRLA.reg = 
    TC_CTRLA_MODE_COUNT16 |    // 16 bit counter
    TC_CTRLA_WAVEGEN_MFRQ |    // Match frequency mode
    TC_CTRLA_PRESCALER_DIV1 |  // Prescaler 1 (giving 48MHz)
    TC_CTRLA_ENABLE;           // Enable bit

  // Set channel 0 compare value to match sample period (50µs)
  TC5->COUNT16.CC[0].reg = (uint16_t) (SystemCoreClock / sampleRate - 1);

  // Get in sync
  TC5_SYNC();
 
  // Configure interrupt settings for TC5
  NVIC_DisableIRQ(TC5_IRQn);
  NVIC_ClearPendingIRQ(TC5_IRQn);
  NVIC_SetPriority(TC5_IRQn, 0);
  NVIC_EnableIRQ(TC5_IRQn);

  // Enable TC5 channel 0 match interrupt
  TC5->COUNT16.INTENSET.bit.MC0 = 1;
  TC5_SYNC();
}

// TC5 global interrupt handler. This callback function is automatically
// set up by the Arduino environment as an interrupt service routine.
// This function must be named exactly like this (do not change).
void TC5_Handler (void)
{
  // Call our own function
  sample_event();

  // Must acknowledge the interrupt request for it to trigger again
  TC5->COUNT16.INTFLAG.bit.MC0 = 1;
}

// Main sample functions. Called in interrupt context once every sample period.
void sample_event()
{
  // Keep track of timing for debugging purposes.
  #ifdef DEBUG
    unsigned long nowt = micros();
    timing = nowt - lastt;
    lastt = nowt;
  #endif

  // Start by initiate a ADC operation immediately followed by DAC 
  // output of the calulated sample from the last event. This will
  // minimize jitter on both ADC and DAC.

  // The ADC source MUX is already configured for A1
  // Start ADC conversion, it will run in the background
  ADC->SWTRIG.bit.START = 1;

  // Set the DAC output value calculated during the last interrupt.
  DAC->DATA.reg = o;

  // Do FIR filtering calculations. This is split in to two parts.

  // This loop utilizes that we have two identical copies of the sample
  // circular buffer. There is always a continous block of valid data
  // at the "next_idx" offset. We do not have to check for wrapping!
  // This saves some precious cycles in this inner loop.

  // These FIR filtering loops use the "fir" pointer directly. That is
  // ok and perfectly safe as the background loop is paused during the
  // interrupt service routine. Thus no risk of it being modified.

  // This is the first half of FIR filtering:
  int32_t acc = 0;
  int i=0, n=next_idx, n2=next_idx+FIR_LEN-1;
  for(; i<(FIR_LEN>>2); i++, n++, n2--) {
    // Convolution. Multiply and accumulate. Take advantage
    // of the symmetry to do two values at the same time.
    acc += (samples[n] + samples[n2]) * fir[i]; 
  }

  // The ADC should have had time to finish now. Do the follow up
  cnt = 0;
  while (ADC->INTFLAG.bit.RESRDY == 0) cnt++;   // Waiting for conversion to complete

  // Get our sample!
  s = ADC->RESULT.reg;
  ADC->INTFLAG.reg = ADC_INTFLAG_RESRDY;  // Clear the Data Ready flag

  // We also want to sample a potentiometer.
  // Alternate between A2, A3 and A4
  int p_pin;
  static int p_sel = 0;
  if(p_sel == 0) {
      p_pin = A3;             // Gain
  } else if(p_sel == 1) {
      p_pin = A4;             // f1
  } else {
      p_pin = A2;             // f2
  }

  // Prepare the input MUX
  ADC->INPUTCTRL.bit.MUXPOS = g_APinDescription[p_pin].ulADCChannelNumber;
  ADC_SYNC();

  // Start ADC conversion, it will run in the background
  ADC->SWTRIG.bit.START = 1;

  // Do more FIR filtering. The second half
  for(; i<(FIR_LEN>>1); i++, n++, n2--) {
    acc += (samples[n] + samples[n2]) * fir[i];
  }

  // The center tap is separately handled
  acc += samples[n] * fir[i];

  // acc has a theoretical maximum value FIR_LEN * 512 * 65536, or 2^8 * 2^9 * 2^16 = 2^33
  // but due to the FIR buffer properties, the maximum should become around 2 * 512 * 65536 = 2^26
  // The gain is up to 2^10, so if the sum is shifted 6 steps giving maximum 2^20 we can
  // safely multiply and stay inside 32 bits (31 signed bits)
  acc >>= 6;

  acc *= gain;

  // We have 4 bits to go to compensate for the gain, and 16 bit shift for the FIR table multiplier.
  // But we want the gain to actually be able to amplify. If we skip shifting 5 steps, the max
  // reading on the gain potentiometer results in 32 times volume.
  int32_t o2 = acc >> (4 + 16 - 5);

  // Clamping of the output
  if(o2 < -511) {
    o = 0;
  } else if(o2 > 511) {
    o = 1023;
  } else {
    o = o2 + 512;
  }
  // The DAC will be updated at the start of the next interrupt to minimize jitter

  // Detect if we are near to clipping/overdrive
  // The tick counters shows how long time ago we last had problems
  if(o > OUTPUT_ERROR_LEVEL_HIGH || o < OUTPUT_ERROR_LEVEL_LOW) {
    output_error_ticks = 0;
  } else {
    output_error_ticks++;
    if(output_error_ticks > 65000)
      output_error_ticks = 65000;
  }
  if(o > OUTPUT_WARNING_LEVEL_HIGH || o < OUTPUT_WARNING_LEVEL_LOW) {
    output_warning_ticks = 0;
  } else {
    output_warning_ticks++;
    if(output_warning_ticks > 65000)
      output_warning_ticks = 65000;
  }

  // Store the new input sample in the buffers
  // (must be done after the whole FIR is calculated)
  int32_t s2 = s - 512;
  samples[next_idx] = s2;
  samples[next_idx+FIR_LEN] = s2;   // Mirrored copy.. but worth it!
  next_idx++;
  if(next_idx >= FIR_LEN)
    next_idx = 0;

  // Follow up on potentiometer ADC conversion
  cnt2 = 0;
  while (ADC->INTFLAG.bit.RESRDY == 0) cnt2++;   // Waiting for conversion to complete
  uint32_t p = ADC->RESULT.reg;
  ADC->INTFLAG.reg = ADC_INTFLAG_RESRDY;  // Clear the Data Ready flag

  // Store the sample in the correct variable, switch to the next input
  if(p_sel == 0) {
      p_gain = p;             // Gain
      p_sel = 1;
  } else if(p_sel == 1) {
      p_f1 = p;               // f1
      p_sel = 2;
  } else {
      p_f2 = p;               // f2
      p_sel = 0;
  }

  // Pre-set MUX to A1 so that we can start sampling immediately at next interrupt
  ADC->INPUTCTRL.bit.MUXPOS = g_APinDescription[A1].ulADCChannelNumber;
  ADC_SYNC();
}

// The background loop!
void loop() {

  #ifdef DEBUG
    // Some timer loop debug info
    Serial.print("Per sample loop time: ");
    Serial.print(timing);
    Serial.print(" us,  ADC wait count 1: ");
    Serial.print(cnt);
    Serial.print(",  count 2: ");
    Serial.print(cnt2);
    Serial.print("\n");
    Serial.print("Sample: ");
    Serial.print(s);
    Serial.print("\n");
    Serial.print("Potentiometers: Gain: ");
    Serial.print(p_gain);
    Serial.print(",  f1: ");
    Serial.print(p_f1);
    Serial.print(",  f2: ");
    Serial.print(p_f2);
    Serial.print("\n");

    // Measure timing
    unsigned long filter_startt = micros();
  #endif

  // Potientiometer input is filtered to remove noise.
  // Accumulation buffers:
  static float g_acc = 0.0f, f1_acc = 0.0f, f2_acc = 0.0f;

  // Handle gain input and activate it
  float g_in = (float)p_gain;
  g_acc = 0.8f * g_acc + 0.2f * g_in;
  gain = (uint32_t)g_acc;

  // Translate frequency potentiometer input to frequencies
  // Lower frequency f1 range 50-1000 Hz
  float f1_in = 50.0f + 950.0f * (float)p_f1 / 1024.0f;
  f1_acc = 0.8f * f1_acc + 0.2f * f1_in;
  float f1 = f1_acc;

  // Upper frequency f2 range split in two halves 400-1000Hz and 1000-4000Hz
  float f2_in = (float)p_f2 / 1024.0f;
  if(f2_in < 0.5f) {
    f2_in = 400.0f + 1200.0f * f2_in; // 0.0 < f2_in < 0.5
  } else {
    f2_in = -2000.0f + 6000.0f * f2_in; // 0.5 < f2_in < 1.0
  }
  f2_acc = 0.8f * f2_acc + 0.2f * f2_in;
  float f2 = f2_acc;

  // Special CW mode if f2 < 1000
  if(f2 < 1000.0f) {
    // f2 is below 1000 Hz, fixed 100Hz bandwidth for CW
    f1 = f2 - 100.0f;
  }

  // Get the FIR tap buffer not currently in use
  int32_t *new_fir = (fir == fir1) ? fir2 : fir1;

  // Run the generation and store in the spare buffer
  prepare_fir(new_fir, f1, f2);

  // Make the new filter live. 32 bit volatile pointer writes and reads are assumed to be atomic!
  fir = new_fir;

  #ifdef DEBUG
    // More timing
    unsigned long filter_endt = micros();

    Serial.print("FIR f1: ");
    Serial.print(f1);
    Serial.print(",  f2: ");
    Serial.print(f2);
    Serial.print(",  calc. time: ");
    Serial.print(filter_endt - filter_startt);
    Serial.print(" us,  gain: ");
    Serial.print(g_acc);
    Serial.print("\n");

    Serial.print("[");
    for(int i=0; i<FIR_LEN_TABLE; i++) {
      Serial.print(fir[i]);
      Serial.print(", ");
    }
    Serial.print("]\n");

  #endif

  // Update DotStar RGB LED. The LED is used to show if we are
  // getting near saturation/clipping. Enabling the DotStar
  // may create a small audible interference on the input sampling.
  // It is most likely caused by the DotStar's built in PWM driver
  // switching the LEDs on and off at about 400 Hz. The frequency
  // seems to be affected by the temperature, so the interference
  // is drifting around, and this is noticeable at high gain.
  // Adjust the gain so that the LED is dark most of the time to
  // get the best quality output audio.
  if(output_error_ticks < 2000) {
    // We have seen error conditions during the last 0.1s
    strip.setPixelColor(0, 255, 0, 0);  // Angry red color on RGB LED
  } else if(output_warning_ticks < 2000) {
    // We have seen warning conditions during the last 0.1s
    strip.setPixelColor(0, 191, 191, 0);  // Yellow color
  } else {
    // All ok, switch the LEDs off to avoid interference on the input
    strip.setPixelColor(0, 0, 0, 0);  // All off, dark means good signal
  }
  strip.show();
}
