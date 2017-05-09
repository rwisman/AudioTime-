package edu.ius.audiotimeplus;

import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;

class AudioIntentReceiver extends BroadcastReceiver {
	int RECORDER_SAMPLERATE = 44100;
	int frequency=2000;
	int waves = 4;
	Context context;
	
	public AudioIntentReceiver(Context context, int recorder_sampleRate, int frequency, int waves){
		RECORDER_SAMPLERATE = recorder_sampleRate;
		this.context=context;
		this.frequency = frequency;
		this.waves = waves;
	}
	
	public AudioIntentReceiver(Context context){
		this.context=context;
	}
	
    @Override public void onReceive(Context context, Intent intent) {
        if (intent.getAction().equals(Intent.ACTION_HEADSET_PLUG)) {
            int state = intent.getIntExtra("state", -1);
            switch (state) {
            case 0: 								// Headset unplugged
                AudioSineWave.stop();
                break;
            case 1: 								// Headset is plugged
                AudioSineWave.start(context, RECORDER_SAMPLERATE, frequency, -1, 0.5, waves);
                break;
            default: 								// Unknown headset state
            }
        }
    }
}