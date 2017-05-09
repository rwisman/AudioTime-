package edu.ius.audiotimeplus;
/*
 * Generates a sine wave at the approximate frequency specified.
 * Because SAMPLES = RECORDER_SAMPLERATE/FREQUENCY yields the same number of samples for a wide range of frequencies (e.g. 44100/3676 = 44100/4009 = 11) 
 * producing the same sine wave.
 */
import android.content.Context;
import android.media.AudioFormat;
import android.media.AudioManager;
import android.media.AudioTrack;

class AudioSineWave {										// Some phones require more than a single wave in buffer (e.g. Nexus 5)
	static AudioTrack audioTrack=null;
	
	public static void start(final Context context, final int RECORDER_SAMPLERATE, final int FREQUENCY, final int LOOPCOUNT, final double VOLUME, final int waves) {
		final int SAMPLES = RECORDER_SAMPLERATE/FREQUENCY;
		AudioManager audioManager = (AudioManager) context.getSystemService(Context.AUDIO_SERVICE);
		audioManager.setStreamVolume(AudioManager.STREAM_MUSIC,
		    (int)(audioManager.getStreamMaxVolume(AudioManager.STREAM_MUSIC)*VOLUME),							// Set to fractional max volume
		    AudioManager.FLAG_SHOW_UI);

		audioTrack = new AudioTrack(AudioManager.STREAM_MUSIC, RECORDER_SAMPLERATE,
			AudioFormat.CHANNEL_OUT_MONO,
			AudioFormat.ENCODING_PCM_16BIT, waves*SAMPLES*2,
			AudioTrack.MODE_STATIC);
 
		(new Thread() {
			public void run() {
				play(waves*SAMPLES, LOOPCOUNT, sineWave(SAMPLES, waves));
			}		
		}).start();
	}
	
	private static byte[] sineWave(int samplesPerWave, int waves) {
		int samples = samplesPerWave*waves;
		final double sample[] = new double[samples];
		final byte sineWave[] = new byte[2 * samples];
		
		double x;
		double xStep = (waves * 2 * Math.PI)/samples;
		int i;

		for (x=0.0, i=0; waves * 2 * Math.PI - x > 0.0001; x=x+xStep, ++i) 
			sample[i] = Math.sin(x);
		
		// Convert normalized samples to 16 bit PCM data
		int idx = 0;
		for (double dVal : sample) {
			short val = (short) (dVal * 32767);
			sineWave[idx++] = (byte) (val & 0x00ff);
			sineWave[idx++] = (byte) ((val & 0xff00) >> 8);
		}
		return sineWave;	
	}
	
	private static void play(int samples, int loopCount, byte[] sineWave) {
		audioTrack.write(sineWave, 0, sineWave.length);
		audioTrack.setLoopPoints(0, samples , loopCount);
		audioTrack.play();
	}

	public static void stop() {
		if(audioTrack != null) {
			audioTrack.setLoopPoints(0, 0 , 0);							// Turn off looping
			audioTrack.play();
			audioTrack.stop();	
		}
		audioTrack=null;
	}
}
