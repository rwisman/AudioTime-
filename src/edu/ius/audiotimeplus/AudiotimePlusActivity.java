/*
 *     Copyright (C) 2013  Raymond Wisman
 * 			Indiana University SE
 * 			November 29, 2013
 * 
 * 	AudioTime+ records, displays, saves, plays and finds dominant frequency of selected audio.  
 *  Connecting a simple circuit (see website) as a headset allows timing with photogates resistance devices.

	The application is designed for use in science education experiments that:
		measure the time interval between two audio events,
		determine the dominant frequency of an interval of audio.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

 */

package edu.ius.audiotimeplus;

import java.text.DecimalFormat;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectOutputStream;
import java.lang.Math;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.app.ProgressDialog;
import android.content.ContentResolver;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.IntentFilter;
import android.graphics.Color;
import android.graphics.DashPathEffect;
import android.graphics.PointF;
import android.net.Uri;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.media.AudioFormat;
import android.media.AudioManager;
import android.media.AudioRecord;
import android.media.AudioTrack;
import android.media.MediaRecorder;
import android.os.Environment;
import android.view.LayoutInflater;
import android.view.MotionEvent;
import android.view.View;
import android.view.GestureDetector.OnGestureListener;
import android.view.GestureDetector.OnDoubleTapListener;
import android.view.GestureDetector;
import android.widget.AdapterView;
import android.widget.ArrayAdapter;
import android.widget.EditText;
import android.widget.ImageButton;
import android.widget.ListView;
import android.view.Menu;
import android.view.MenuItem;
import android.widget.TextView;

import com.androidplot.Plot;
import com.androidplot.ui.*;
import com.androidplot.util.PixelUtils;
import com.androidplot.xy.BoundaryMode;
import com.androidplot.xy.LineAndPointFormatter;
import com.androidplot.xy.RectRegion;
import com.androidplot.xy.SimpleXYSeries;
import com.androidplot.xy.ValueMarker;
import com.androidplot.xy.XYPlot;
import com.androidplot.xy.XValueMarker;
import com.androidplot.xy.XYRegionFormatter;
import com.androidplot.xy.XYStepMode;
import com.androidplot.util.ValPixConverter;

import edu.ius.fft.FFT;
import edu.ius.fftresult.FFTresult;

public class AudiotimePlusActivity extends Activity implements OnGestureListener, OnDoubleTapListener {
	private static final int MAXSAMPLES = 65536;
	private static final int SERIES_SIZE = 200;
	private static final long ELAPSEDTIME = 100l;

	private static final int ABOUT = 0;
	private static final int INFO = 1;

	private static final int RECORDER_BPP = 16;
	private static final String AUDIO_RECORDER_FILE_EXT_WAV = ".wav";
	private static final String AUDIO_RECORDER_FILE_EXT_MAG = ".mag";
	private static final String AUDIO_RECORDER_FOLDER = "AudioTimePlus";
	private static final int RECORDER_SAMPLERATE = 44100;
	private static final int SINEWAVEHZ = 4000;											// Approximate
	private static final double ONESAMPLETIME = 1.0/RECORDER_SAMPLERATE;
	private static final int SAMPLES_PER_ONEHUNDREDTH_SECOND = RECORDER_SAMPLERATE/100;
	private static final int RECORDER_CHANNELS = AudioFormat.CHANNEL_IN_MONO;
	private static final int RECORDER_AUDIO_ENCODING = AudioFormat.ENCODING_PCM_16BIT;
	private static final float INITIAL_DOMAIN_SIZE = 5f;								// 5s. of recording
	private static final String AUDIO_RECORDER_TEMP_FILE = "AudioTimePlus_runtime_data.tmp";
	private static final String[] DIALOGMENU = new String[] { "About", "Info" };

	private final Activity activity = this;

	private static float maxX = 0f;
	private static AudioRecord recorder = null;
	private static int bufferSize = RECORDER_SAMPLERATE;											// 1/2 second of data								
	private static Thread threadRecord = null, threadPlay = null, threadFFT=null, threadReload=null, threadRedraw=null;
	
	private static boolean isRecording = false;
	private static boolean isPlaying = false;
	private static boolean isReloading = false;
	private static boolean isDrawing = false;

	private static XYPlot dBPlot = null;
	private static SimpleXYSeries dBSeries = null;

	private static PointF minXY = new PointF(0, -32768);
	private static PointF maxXY = new PointF(0, 32767);
	private static GestureDetector detector;
	private LineAndPointFormatter markedFormatter;
	private XYRegionFormatter markedRegionFormatter;
	private RectRegion markedRegion, markedFFTRegion=null;
	private XValueMarker endFFTMarker=null;
	
	private FFTresult fftResult;
    private ProgressDialog progDialog;
    
	// Definition of the touch states
	static final int NONE = 0;
	static final int ONE_FINGER_DRAG = 1;
	static final int ONE_FINGER_ADJUST = 2;
	static final int TWO_FINGERS_DRAG = 3;
	static int mode = NONE;

	static PointF firstFinger;
	static float distBetweenFingers;

	private static XValueMarker markerLeft = null, markerRight = null, markerAdjusted = null;

	private static long lastTime=0l;
	
	private AudioIntentReceiver audioIntentReceiver=null;

	@SuppressWarnings("deprecation")
	public void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);

		detector = new GestureDetector(this, this);

		setContentView(R.layout.audiotime);
		dBPlot = (XYPlot) findViewById(R.id.dBPlot);

		dBPlot.setDomainStepMode(XYStepMode.INCREMENT_BY_VAL);
		dBPlot.setDomainStepValue(1);

		dBPlot.getGraphWidget().setTicksPerRangeLabel(3);
		dBPlot.getGraphWidget().setTicksPerDomainLabel(1);
		dBPlot.getGraphWidget().getBackgroundPaint().setColor(Color.TRANSPARENT);
		dBPlot.getGraphWidget().setRangeValueFormat(new DecimalFormat("#####"));
		dBPlot.getGraphWidget().setDomainValueFormat(new DecimalFormat("###.#####"));
		dBPlot.getGraphWidget().setRangeLabelWidth(25);
		dBPlot.setBorderStyle(Plot.BorderStyle.NONE, null, null); 
		dBPlot.getLegendWidget().setPadding(100, 1, 1, 1);

		dBPlot.setDomainBoundaries(0, INITIAL_DOMAIN_SIZE, BoundaryMode.FIXED);
		dBPlot.setRangeBoundaries(-32768, 32767, BoundaryMode.AUTO);
		dBPlot.setRangeLabel(getString(R.string.range_label));
		dBPlot.setDomainLabel(getString(R.string.domain_label));

		markedFormatter = new LineAndPointFormatter(Color.rgb(220, 25, 20), Color.rgb(220, 25, 20), null, null);

		startReloadThread();
		startRedrawThread(); 
		setButtonHandlers();
		enableButtons(true);	

		audioIntentReceiver = new AudioIntentReceiver(this, RECORDER_SAMPLERATE, SINEWAVEHZ, 4);	
	    IntentFilter filter = new IntentFilter(Intent.ACTION_HEADSET_PLUG);
	    registerReceiver(audioIntentReceiver, filter);
	    
		openInitialScreen();
	}
    
	@Override
	protected void onStop()
	{
	    super.onStop();
	    unregisterReceiver(audioIntentReceiver);
	    AudioSineWave.stop();
	}
	
	@Override public void onResume() {
	    super.onResume();
	    IntentFilter filter = new IntentFilter(Intent.ACTION_HEADSET_PLUG);
	    registerReceiver(audioIntentReceiver, filter);
	}

    public boolean onCreateOptionsMenu(Menu menu) {
		menu.add(0, ABOUT, 0, DIALOGMENU[ABOUT]);
		menu.add(0, INFO, 0, DIALOGMENU[INFO]);
		return true;
	}

	public boolean onOptionsItemSelected(MenuItem item) {
		switch (item.getItemId()) {
		case ABOUT:
			AboutDialog about = new AboutDialog(this);
			about.setTitle("About AudioTime+");
			about.show();
			break;
		case INFO:
			InfoDialog info = new InfoDialog(this);
			info.setTitle("Info AudioTime+");
			info.show();
			break;
		}
		return true;
	}
	
	private void openInitialScreen() {
	    Intent intent = getIntent();
	    String action = intent.getAction();
	    if (!action.equals(Intent.ACTION_VIEW)) {
	    	openLastSession();							// Started directly by user
	    	return;
	    }

	    Uri uri = intent.getData();						// Started from another app
		byte data[]=new byte[bufferSize];
		byte yValue[]=new byte[2];
		BufferedOutputStream osRAW = null;
		BufferedOutputStream osMINMAX = null;
		int read=0;

		WaveHeader waveHeader = new WaveHeader();
		InputStream in=null;
		try {
			ContentResolver cr = getContentResolver();
			in = cr.openInputStream(uri);
			waveHeader.read(in);
		}
		catch(Exception e){
			AlertDialog alertDialog = new AlertDialog.Builder(this).create();
			alertDialog.setTitle("Error");
			alertDialog.setMessage("WAV file incorrect formatting: "+uri.toString());
			alertDialog.setButton(DialogInterface.BUTTON_POSITIVE, "OK", new DialogInterface.OnClickListener() {
				public void onClick(DialogInterface dialog, int i) { }
				});
			alertDialog.show();
			e.printStackTrace();
		}
		
		dBPlot.setTitle(getString(R.string.app_name) + " " + uri.toString());

		try {
			osRAW = new BufferedOutputStream(new FileOutputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
			osMINMAX = new BufferedOutputStream(new FileOutputStream(getTempFilename("MINMAX"+AUDIO_RECORDER_TEMP_FILE)));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		
		try {
			int y, minY=Integer.MAX_VALUE, maxY=-Integer.MAX_VALUE;
			double minYtime=0, maxYtime=0;
			long runningCount=0;
			double x = 0;

			while((read=in.read(data, 0, bufferSize)) != -1)  {
				osRAW.write(data, 0, read);
				
				int i = 0;
				while (i < read) {																		// Compress keeping min & max values over SAMPLES_PER_ONEHUNDREDTH_SECOND sample length intervals
					y = (int) ((data[i + 1] << 8) | data[i]);
					
					if(y<minY) {
						minY=y;
						minYtime=x;
					}
					if(y>maxY) {
						maxY=y;
						maxYtime=x;
					}
					i=i+2;
					runningCount = runningCount + 2;
					
					if(runningCount % SAMPLES_PER_ONEHUNDREDTH_SECOND == 0) 							// SAMPLES_PER_ONEHUNDREDTH_SECOND samples = .01s 
					  try {
						if( minYtime < maxYtime) {  
							yValue[0] = (byte)(minY & 0xff);
							yValue[1] = (byte)((minY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
							
							yValue[0] = (byte)(maxY & 0xff);
							yValue[1] = (byte)((maxY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
						}
						else { 
							yValue[0] = (byte)(maxY & 0xff);
							yValue[1] = (byte)((maxY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
							
							yValue[0] = (byte)(minY & 0xff);
							yValue[1] = (byte)((minY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
						}	
						minY=Integer.MAX_VALUE;
						maxY=-Integer.MAX_VALUE;
					  } catch (IOException e) {
						  e.printStackTrace();
					  }
					x = x + ONESAMPLETIME;
				}
				
			}
		} 
		catch (IOException e) {
				e.printStackTrace();
		}
		
		float duration = (float)waveHeader.getNumBytes()/2/RECORDER_SAMPLERATE;
		
		dBPlot.setDomainBoundaries(0, duration, BoundaryMode.FIXED);
 		minXY = new PointF(0, -32768); 
		maxXY = new PointF(duration, 32767); 
		maxX = maxXY.x;

		try {
			osRAW.close();
			osMINMAX.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

		reloaddBSeries();
	}
	
	private void openLastSession() {
		File in = null;
		try {
			in = new File(getTempFilename(AUDIO_RECORDER_TEMP_FILE));
			if(in.exists()) {
				minXY = new PointF(0, -32768); 
				float x = ((float)in.length()/2)/RECORDER_SAMPLERATE;
				maxXY = new PointF((float)x, 32767); 
				maxX = maxXY.x;

				reloaddBSeries();
				redrawPlot();
			}
			else splashScreen();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	private void splashScreen() {																	// Generate and display sine wave 0..2*pi for testing and initial screen
		
		byte data[] = new byte[2];
		String filename = getTempFilename(AUDIO_RECORDER_TEMP_FILE);
		BufferedOutputStream os = null;
		float xStep = 1f/RECORDER_SAMPLERATE;

		try {
			os = new BufferedOutputStream(new FileOutputStream(filename));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		double x;

		dBPlot.setDomainBoundaries(0, (float) (3*Math.PI), BoundaryMode.FIXED);
		
		for(x = 0; x <  Math.PI*2; x=x+xStep) { 
			short y = (short)(Math.sin(x)*32767);
			data[1] = (byte)((y & 0xff00) >> 8);
			data[0] = (byte)(y & 0x00ff);

			try {
				os.write(data, 0, 2);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		try {
			os.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
 		minXY = new PointF(0, -32768); 
		maxXY = new PointF((float)x, 32767); 
		maxX = maxXY.x;

		reloaddBSeries();
	}

	private void findPeakinWindow(boolean findThreshold) {
		BufferedInputStream in = null;
		byte[] data = new byte[2];

		synchronized (dBPlot) {
			long samplesToRead = (long) (RECORDER_SAMPLERATE * (maxXY.x - minXY.x));
			double x = minXY.x;
			double xStep=0;
			double markX;
			int markY;
			long samplesRead = 0;
			int y=0;
			double startX=0;
			int threshold=0;
			
			if(findThreshold) {
				markY=Integer.MAX_VALUE;
				markX=Integer.MAX_VALUE;
			}
			else {
				markY=Integer.MIN_VALUE;
				markX=Integer.MIN_VALUE;
			}
			int p0=Integer.MAX_VALUE,p1=Integer.MAX_VALUE,p2=Integer.MAX_VALUE;
			int maxPeakY=Integer.MIN_VALUE, minPeakY=Integer.MAX_VALUE;
			double maxPeakX=(double)Integer.MIN_VALUE, minPeakX=(double)Integer.MAX_VALUE;
			int currentPeakY=Integer.MAX_VALUE;

			try {
				in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));

				in.skip((int) (RECORDER_SAMPLERATE * minXY.x) * 2); 				// Skip 2 bytes/sample

				xStep = (double) (maxXY.x - minXY.x) / samplesToRead;
				while (in.read(data, 0, 2) != -1 && samplesRead <= samplesToRead) {
					y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 				// Little endian
					y = y <= 32767 ? y : y - 65535;

					if(p1 > 0 && p0<p1 && p1>p2 && minPeakY>p1) {					// Is p1 an inflection point and smaller than seen so far
						minPeakY = p1;
						minPeakX = x;
					}
					p0=p1;
					p1=p2;
					p2=y;
							
					if( y > maxPeakY ) {
						maxPeakY=y;
						maxPeakX=x;
					}						
					samplesRead++;
					x = x + xStep;
				}
				in.close();
				
				if(findThreshold) {													// Make 2nd pass starting at max peak
					in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
					threshold=maxPeakY-(int)((maxPeakY-minPeakY)*0.80);

					startX=maxPeakX;
					
					if(maxPeakX > minPeakX)
						startX=minXY.x;
					
					in.skip((int) (RECORDER_SAMPLERATE * startX) * 2); 				// Skip 2 bytes/sample
					
					samplesToRead = (long) (RECORDER_SAMPLERATE * ( minPeakX - startX));
					
					y=Integer.MAX_VALUE;
					
					samplesRead = 0;
					x=startX;
					p0=Integer.MAX_VALUE;
					p1=Integer.MAX_VALUE;
					p2=Integer.MAX_VALUE;

					xStep = (double) (minPeakX-startX) / samplesToRead;
					while (in.read(data, 0, 2) != -1 && samplesRead <= samplesToRead && currentPeakY > threshold) {
						y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 				// Little endian
						y = y <= 32767 ? y : y - 65535;
						
						if(p1 > 0 && p0<p1 && p1>p2)									// Is p1 an inflection point and smaller than seen so far
							currentPeakY = p1;

						p0=p1;
						p1=p2;
						p2=y;
														
						samplesRead++;
						x = x + xStep;
					}
					in.close();
					markX = x-xStep;
				}
				else
					markX = maxPeakX;
				
				XValueMarker marker = markerAtX(markX, Color.YELLOW);

				if (markerLeft == null && markerRight == null) {
					markerLeft = marker;
				}
				else if (marker.getValue().floatValue() > markerLeft.getValue().floatValue())
					markerRight = marker;
				else {
					markerRight = markerLeft;
					markerLeft = marker;
				}

				if(markerLeft != null && markerRight != null) {
					removeMarkers();
					markerAtX(markerLeft.getValue().floatValue(), Color.YELLOW);
					markerAtX(markerRight.getValue().floatValue(), Color.YELLOW);
					addMarkedRegion();
				}

			} catch (FileNotFoundException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	private void setButtonHandlers() {

		((ImageButton) findViewById(R.id.btnReset)).setOnClickListener(new View.OnClickListener() {
			@Override
			public void onClick(View arg0) {
				minXY.x = 0f;
				maxXY.x = maxX;
				reloaddBSeries();
				redrawPlot();
			}
		});

		((ImageButton) findViewById(R.id.btnFindPeak)).setOnClickListener(new View.OnClickListener() {
			@Override
			public void onClick(View arg0) {
				findPeakinWindow(false);
			}
		});
		
		((ImageButton) findViewById(R.id.btnFindThreshold)).setOnClickListener(new View.OnClickListener() {
			@Override
			public void onClick(View arg0) {
				findPeakinWindow(true);
			}
		});
		
		((ImageButton) findViewById(R.id.btnSave)).setOnClickListener(new View.OnClickListener() {		 
			@Override
			public void onClick(View arg0) {
				LayoutInflater li = LayoutInflater.from(activity);
				View promptsView = li.inflate(R.layout.filename, null);
 
				AlertDialog.Builder alertDialogBuilder = new AlertDialog.Builder(activity);
 
				alertDialogBuilder.setView(promptsView);
 
				final EditText userInput = (EditText) promptsView.findViewById(R.id.editTextDialogUserInput);
				userInput.setText(getFilename(AUDIO_RECORDER_FILE_EXT_WAV), TextView.BufferType.EDITABLE);
 
				alertDialogBuilder
					.setCancelable(false)
					.setPositiveButton("OK",
					  new DialogInterface.OnClickListener() {
					    public void onClick(DialogInterface dialog,int id) {
					    	saveRecording(userInput.getText().toString());
					    }
					  })
					.setNegativeButton("Cancel",
					  new DialogInterface.OnClickListener() {
					    public void onClick(DialogInterface dialog,int id) {
						dialog.cancel();
					    }
					  });
 
				AlertDialog alertDialog = alertDialogBuilder.create();
 				alertDialog.show();
			}
		});

		((ImageButton) findViewById(R.id.btnRecord))
				.setOnClickListener(new View.OnClickListener() {
					public void onClick(View arg0) {
						if ("isNotChecked".equals(arg0.getTag())) {
							arg0.setTag("isChecked");
							enableButtons(false);
							((ImageButton) findViewById(R.id.btnPlay))
									.setEnabled(false);
							((ImageButton) findViewById(R.id.btnPlay))
									.setImageResource(R.drawable.play_recording_disabled);
							((ImageButton) findViewById(R.id.btnRecord))
									.setImageResource(R.drawable.stop_recording);
							((TextView) findViewById(R.id.txtSave))
									.setText(null);
							startRecording();
						} else {
							arg0.setTag("isNotChecked");
							enableButtons(true);
							((ImageButton) findViewById(R.id.btnPlay))
									.setEnabled(true);
							((ImageButton) findViewById(R.id.btnPlay))
									.setImageResource(R.drawable.play_recording);
							((ImageButton) findViewById(R.id.btnRecord))
									.setEnabled(true);
							((ImageButton) findViewById(R.id.btnRecord))
									.setImageResource(R.drawable.start_recording);

							stopRecording();
						}
					}
				});

		((ImageButton) findViewById(R.id.btnPlay))
				.setOnClickListener(new View.OnClickListener() {
					public void onClick(View arg0) {
						if ("isNotChecked".equals(arg0.getTag())) {
							arg0.setTag("isChecked");
							enableButtons(false);
							((ImageButton) findViewById(R.id.btnPlay))
									.setEnabled(true);
							((ImageButton) findViewById(R.id.btnPlay))
									.setImageResource(R.drawable.play_recording_stop);
							((ImageButton) findViewById(R.id.btnRecord))
									.setEnabled(false);
							((ImageButton) findViewById(R.id.btnRecord))
									.setImageResource(R.drawable.start_recording_disabled);
							startPlaying();
						} else {
							arg0.setTag("isNotChecked");
							stopPlaying();
						}
					}
				});

		((ImageButton) findViewById(R.id.btnLeft))
		.setOnClickListener(new View.OnClickListener() {
			public void onClick(View arg0) {
				maxXY.x=(maxXY.x-minXY.x);
				minXY.x=0f;
				reloaddBSeries();
				redrawPlot();
			}
		});

		((ImageButton) findViewById(R.id.btnRight))
		.setOnClickListener(new View.OnClickListener() {
			public void onClick(View arg0) {
				minXY.x=maxX-(maxXY.x-minXY.x);
				maxXY.x=maxX;
				reloaddBSeries();
				redrawPlot();
			}
		});

		((ImageButton) findViewById(R.id.btnRange))
				.setOnClickListener(new View.OnClickListener() {
					public void onClick(View arg0) {
						if ("isNotChecked".equals(arg0.getTag())) {
							arg0.setTag("isChecked");
							dBPlot.setRangeBoundaries(-32768, 32767,
									BoundaryMode.FIXED);
							((ImageButton) findViewById(R.id.btnRange))
									.setImageResource(R.drawable.fixed_range);
						} else {
							arg0.setTag("isNotChecked");
							dBPlot.setRangeBoundaries(-32768, 32767,
									BoundaryMode.AUTO);
							((ImageButton) findViewById(R.id.btnRange))
									.setImageResource(R.drawable.auto_range);
						}
						redrawPlot();
					}
				});

		((ImageButton) findViewById(R.id.btnHelp))
				.setOnClickListener(new View.OnClickListener() {
					public void onClick(View arg0) {
						AlertDialog.Builder builder = new AlertDialog.Builder(activity);

						final ListView modeList = new ListView(activity);

						ArrayAdapter<String> modeAdapter = new ArrayAdapter<String>(
								activity, android.R.layout.simple_list_item_1,
								android.R.id.text1, DIALOGMENU);
						modeList.setAdapter(modeAdapter);

						builder.setView(modeList);
						final Dialog dialog = builder.create();
						dialog.setCanceledOnTouchOutside(true);

						dialog.show();
						modeList.setOnItemClickListener(new android.widget.AdapterView.OnItemClickListener() {
							@Override
							public void onItemClick(AdapterView<?> parent,
									View view, int position, long id) {
								switch (position) {
								case ABOUT:
									AboutDialog about = new AboutDialog(activity);
									about.setTitle("About AudioTime+");
									about.show();
									break;
								case INFO:
									InfoDialog info = new InfoDialog(activity);
									info.setTitle("Info AudioTime+");
									info.show();
									break;
								}
								dialog.dismiss();
							}
						});
					}
				});
		
		((ImageButton) findViewById(R.id.btnFFT))
		.setOnClickListener(new View.OnClickListener() {
			public void onClick(View arg0) {				
				markFFT();
				showDialog(0);
				runFFT();
			}
		});
	}
	
	private void enableButton(int id, boolean isEnable) {
		((ImageButton) findViewById(id)).setEnabled(isEnable);
	}

	private void enableButtons(boolean isEnabled) {
		enableButton(R.id.btnReset, isEnabled);
		enableButton(R.id.btnSave, isEnabled);
		enableButton(R.id.btnLeft, isEnabled);
		enableButton(R.id.btnRight, isEnabled);
		enableButton(R.id.btnFFT, isEnabled);
		enableButton(R.id.btnFindPeak, isEnabled);
		enableButton(R.id.btnFindThreshold, isEnabled);
	}

	private void markFFT() {
		long samplesAvailable = (long) (RECORDER_SAMPLERATE * (maxXY.x - minXY.x));
		
		int SAMPLES;
		
		if(samplesAvailable > MAXSAMPLES)
			SAMPLES = (int)(samplesAvailable/MAXSAMPLES)*MAXSAMPLES;								// Multiple of MAXSAMPLES
		else
			SAMPLES =  (int) Math.pow(2.0, (int)(Math.log10(samplesAvailable) / Math.log10(2))); 	// power of 2
		
//		Log.d("*******markFFT SAMPLES maxXY.x minXY.x ", SAMPLES+" "+maxXY.x +" " + minXY.x);
				
		float end = minXY.x+(float)SAMPLES/RECORDER_SAMPLERATE;
		endFFTMarker = markerAtX(end, Color.WHITE);
		markedRegionFormatter = new XYRegionFormatter(Color.WHITE);
		markedRegionFormatter.getPaint().setAlpha(75);
		
		markedFFTRegion = new RectRegion(minXY.x, end, Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 
						" Interval " + (end - minXY.x));
		markedFormatter.addRegion(markedFFTRegion, markedRegionFormatter);
	}
	
	private void unmarkFFT() {
		markedFormatter.removeRegion(markedFFTRegion);
		dBPlot.removeMarker(endFFTMarker);
		markedFFTRegion=null;
		endFFTMarker=null;
		redrawPlot();
	}
	
    @Override
    protected Dialog onCreateDialog(int id) {
        switch(id) {
        case 0:                      // Spinner
            progDialog = new ProgressDialog(this);
            progDialog.setCanceledOnTouchOutside(true);
            progDialog.setProgressStyle(ProgressDialog.STYLE_SPINNER);
            progDialog.setMessage("Computing FFT...");
			progDialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
				@Override
				public void onDismiss(final DialogInterface dialog) {
        			unmarkFFT();
				}
			});
            return progDialog;
        default:
            return null;
        }
    }
    
    final Handler handler = new Handler() {
        @SuppressWarnings("deprecation")
		public void handleMessage(Message msg) {
            dismissDialog(0);
            progDialog = null;
        }
    };


	private void runFFT() {
		threadFFT = new Thread(new Runnable() {

			@Override
			public void run() {
				String s = FFT();
	            Message msg = handler.obtainMessage();
	            handler.sendMessage(msg);
				displayFFT(s);
				threadFFT = null;
			}
		}, "AudioTime+ FFT Thread");

		threadFFT.start();
	}
	
	private void displayFFT(String displayString) {
		final String s=displayString;
		
		runOnUiThread(new Runnable() {
			public void run() {
				AlertDialog.Builder alert  = new AlertDialog.Builder(activity);
				
				alert.setTitle(getString(R.string.fft_title));
				alert.setMessage(s + "\n\nView spectrum?");
 
				alert
					.setPositiveButton("Yes", new DialogInterface.OnClickListener() {
				        public void onClick(DialogInterface dialog, int which) {
				        	
				        	final Intent intent = new Intent("edu.ius.audiospectrum.ACTION");
				        	String filename = getFilename(AUDIO_RECORDER_FILE_EXT_MAG);
				        	
				            intent.putExtra("FFTresult", filename);
				            
			        		try {
			        			ObjectOutputStream out = new ObjectOutputStream(new FileOutputStream(filename));
			        			out.writeObject(fftResult);
			        			out.flush();
			        			out.close();
			        		} catch (FileNotFoundException e) {
			        			e.printStackTrace();
			        		} catch (IOException e) {
			        			e.printStackTrace();
			        		}
			            	startActivity(intent);
				        }
				    })
				    .setNegativeButton("No",new DialogInterface.OnClickListener() {
				    	public void onClick(DialogInterface dialog,int id) {
						dialog.cancel();
					}
				});
				
				AlertDialog alertDialog = alert.create();
				
				alertDialog.setOnDismissListener(new DialogInterface.OnDismissListener() {
					@Override
					public void onDismiss(final DialogInterface dialog) {
	        			unmarkFFT();
					}
				});
 				alertDialog.show();
			}
		});
	}


	private String FFT() {
		long samplesAvailable = (long) (RECORDER_SAMPLERATE * (maxXY.x - minXY.x));
		int sampleRate = RECORDER_SAMPLERATE;
		
		int samples;
		if(samplesAvailable > MAXSAMPLES)
			samples = (int)(samplesAvailable/MAXSAMPLES)*MAXSAMPLES;								// Multiple of MAXSAMPLES
		else
			samples =  (int) Math.pow(2.0, (int)(Math.log10(samplesAvailable) / Math.log10(2))); 	// power of 2
		
//		Log.d("*****FFT() ", samplesAvailable +" " + samples+" "+maxXY.x+" "+minXY.x);
		
		BufferedInputStream in = null;
		byte[] data = new byte[2];
		
		int total = 0, n = 0, index = 0;
		int N = Math.min(samples, MAXSAMPLES);
		int y;
		double audioData[] = new double[N];	
		int halfSpectrum = sampleRate / 2;
		double average[] = new double[Math.min(halfSpectrum, N/2)];
		double mag[];
		
		fftResult = null;

		try {
			in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));

			in.skip((int) (RECORDER_SAMPLERATE * minXY.x) * 2); 					// Skip  2 bytes/sample

			while (in.read(data, 0, 2) != -1 && total < samples) {
				y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); // Little endian
				y = y <= 32767 ? y : y - 65535;
				audioData[index] = y;
				if( index == N - 1) {
					mag = (new FFT()).fft(audioData);
					fftResult = new FFTresult(mag, sampleRate, N);
					for(int i=0; i < fftResult.magnitudeFFT.length; i++)
						average[i] = average[i]+fftResult.magnitudeFFT[i];
					n++;
					index = 0;
				}
				else	
					index++;
				total++;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		if( fftResult == null ) {
			return "Error\n\nFFT failed";
		}

		for(int i=0; i < fftResult.magnitudeFFT.length; i++)					// Ensemble spectral averaging
			average[i] = average[i]/n;
		
		fftResult.setMagnitudeFFT(average);

		int max_i[] = {0, 0, 0, 0};
		double max = 0;
		for (int j = 0; j < max_i.length; j++) {
			max = fftResult.magnitudeFFT[1];
			int indexOfMax = 1;
			for (int k = 1; k < fftResult.magnitudeFFT.length; k++) {
				if (max < fftResult.magnitudeFFT[k]) {
					max = fftResult.magnitudeFFT[k];
					indexOfMax = k;
				}
			}
			max_i[j] = indexOfMax;

			if (indexOfMax >= 0 && indexOfMax < fftResult.magnitudeFFT.length && fftResult.magnitudeFFT[indexOfMax] > 0)
					fftResult.magnitudeFFT[indexOfMax] = -fftResult.magnitudeFFT[indexOfMax];
		}

		for (int j = 0; j < max_i.length; j++)
				if (max_i[j] >= 0 && max_i[j] < fftResult.magnitudeFFT.length)
					fftResult.magnitudeFFT[max_i[j]] = Math.abs(fftResult.magnitudeFFT[max_i[j]]);
		
		/* Frequency = Fs * max / N
             Fs = sample rate (Hz)
             max = index of peak
             N = number of points in FFT
          */

		double frequency[] = {fftResult.frequencyFFT[max_i[0]], fftResult.frequencyFFT[max_i[1]], fftResult.frequencyFFT[max_i[2]], fftResult.frequencyFFT[max_i[3]]};
		return getString(R.string.frequency)+"\n" + frequency[0]+" \t"+frequency[1]+" \t"+frequency[2]+" \t"+frequency[3]+"\n"+
			getString(R.string.window)+" " +(int)(minXY.x*10000)/10000f+"s.."+(int)((minXY.x+(float)samples/RECORDER_SAMPLERATE)*10000)/10000f+"s\n"+
			getString(R.string.samples)+" "+samples;
	}

	private void startPlaying() {

		isPlaying = true;

		threadPlay = new Thread(new Runnable() {

			@Override
			public void run() {
				play();
			}
		}, "AudioTime+ Play Thread");

		threadPlay.start();
	}

	private void stopPlaying() {
		runOnUiThread(new Runnable() {
			public void run() {
				isPlaying = false;
				((ImageButton) findViewById(R.id.btnRecord)).setEnabled(true);
				((ImageButton) findViewById(R.id.btnRecord))
						.setImageResource(R.drawable.start_recording);
				((ImageButton) findViewById(R.id.btnPlay))
						.setImageResource(R.drawable.play_recording);
				((ImageButton) findViewById(R.id.btnPlay))
						.setTag("isNotChecked");
				enableButtons(true);
				threadPlay = null;
			}
		});
	}

	private void play() {
		
		int playBufferSize=1000;															// Small buffer size plays shorter sound tracks. Not sure why.

		float xStep = playBufferSize/((float)RECORDER_SAMPLERATE*2); 						// 2 bytes/sample

		AudioTrack audioTrack = new AudioTrack(AudioManager.STREAM_MUSIC,
				RECORDER_SAMPLERATE, AudioFormat.CHANNEL_OUT_MONO,
				AudioFormat.ENCODING_PCM_16BIT, playBufferSize,
				AudioTrack.MODE_STREAM);

		if(+audioTrack.getState() != AudioTrack.STATE_INITIALIZED) return;
		
		audioTrack.play();

		BufferedInputStream in = null;
		byte[] audioData = new byte[playBufferSize];
		float x = minXY.x;
		int read;

		try {
			in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));

			in.skip((int) (RECORDER_SAMPLERATE * minXY.x) * 2); 

			XValueMarker marker = markerAtX(x, Color.WHITE);
			
			while ((read = in.read(audioData, 0, playBufferSize)) != -1 && x <= maxXY.x && isPlaying) {	// Last may be partial buffer but play full anyway since buffer so small
				dBPlot.addMarker(marker);
				audioTrack.write(audioData, 0, read);
				audioTrack.flush();
				x = x + xStep;
				dBPlot.removeMarker(marker);
				marker = markerAtX(x, Color.WHITE);										// When other markers displayed causes dBPlot race condition but synchronizing 
			}																			// causes jitter on audio output. 
			dBPlot.removeMarker(marker);

			in.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (IllegalStateException e) {
			e.printStackTrace();
		}

		audioTrack.release();
		stopPlaying();
	}

	private String getFilename(String ext) {
		String filepath = Environment.getExternalStorageDirectory().getPath();
		File file = new File(filepath, AUDIO_RECORDER_FOLDER);

		if (!file.exists()) {
			file.mkdirs();
		}
		return (file.getAbsolutePath() + "/" + System.currentTimeMillis() + ext);
	}

	private void saveRecording(String outFilename) {
		BufferedInputStream in = null;
		FileOutputStream out = null;
		long totalAudioLen = 0;
		long totalDataLen = totalAudioLen + 36;
		long longSampleRate = RECORDER_SAMPLERATE;
		int channels = 1;
		long byteRate = RECORDER_BPP * RECORDER_SAMPLERATE * channels / 8;

		byte[] audioData = new byte[bufferSize];										// 2 bytes/sample

		float x = minXY.x;
		float xStep = bufferSize/((float)RECORDER_SAMPLERATE*2); 

		int read;

		try {
			in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
			out = new FileOutputStream(outFilename);
			totalAudioLen = (int) (RECORDER_SAMPLERATE * (maxXY.x-minXY.x) * 2); 
			totalDataLen = totalAudioLen + 36;

			WriteWaveFileHeader(out, totalAudioLen, totalDataLen,
					longSampleRate, channels, byteRate);

			in.skip((int) (RECORDER_SAMPLERATE * minXY.x) * 2); 						// 2 bytes/sample
			
			while ((read = in.read(audioData, 0, bufferSize)) != -1 && x <= maxXY.x) {
				if (maxXY.x - x < xStep)
					read = (int) (bufferSize * (maxXY.x - x))*2; 						// Partial buffer to write
				out.write(audioData, 0, read);
				x = x + xStep;
			}
			in.close();
			out.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void WriteWaveFileHeader(FileOutputStream out, long totalAudioLen,
			long totalDataLen, long longSampleRate, int channels, long byteRate)
			throws IOException {

		byte[] header = new byte[44];

		header[0] = 'R'; // RIFF/WAVE header
		header[1] = 'I';
		header[2] = 'F';
		header[3] = 'F';
		header[4] = (byte) (totalDataLen & 0xff);
		header[5] = (byte) ((totalDataLen >> 8) & 0xff);
		header[6] = (byte) ((totalDataLen >> 16) & 0xff);
		header[7] = (byte) ((totalDataLen >> 24) & 0xff);
		header[8] = 'W';
		header[9] = 'A';
		header[10] = 'V';
		header[11] = 'E';
		header[12] = 'f'; // 'fmt ' chunk
		header[13] = 'm';
		header[14] = 't';
		header[15] = ' ';
		header[16] = 16; // 4 bytes: size of 'fmt ' chunk
		header[17] = 0;
		header[18] = 0;
		header[19] = 0;
		header[20] = 1; // format = 1
		header[21] = 0;
		header[22] = (byte) channels;
		header[23] = 0;
		header[24] = (byte) (longSampleRate & 0xff);
		header[25] = (byte) ((longSampleRate >> 8) & 0xff);
		header[26] = (byte) ((longSampleRate >> 16) & 0xff);
		header[27] = (byte) ((longSampleRate >> 24) & 0xff);
		header[28] = (byte) (byteRate & 0xff);
		header[29] = (byte) ((byteRate >> 8) & 0xff);
		header[30] = (byte) ((byteRate >> 16) & 0xff);
		header[31] = (byte) ((byteRate >> 24) & 0xff);
		header[32] = (byte) (channels * 16 / 8); // block align
		header[33] = 0;
		header[34] = RECORDER_BPP; // bits per sample
		header[35] = 0;
		header[36] = 'd';
		header[37] = 'a';
		header[38] = 't';
		header[39] = 'a';
		header[40] = (byte) (totalAudioLen & 0xff);
		header[41] = (byte) ((totalAudioLen >> 8) & 0xff);
		header[42] = (byte) ((totalAudioLen >> 16) & 0xff);
		header[43] = (byte) ((totalAudioLen >> 24) & 0xff);

		out.write(header, 0, 44);
	}

	private void startRecording() {

		recorder = new AudioRecord(MediaRecorder.AudioSource.MIC,
				RECORDER_SAMPLERATE, RECORDER_CHANNELS,
				RECORDER_AUDIO_ENCODING, bufferSize);

		cleardBPlot();
		deleteTempFile(AUDIO_RECORDER_TEMP_FILE);
		deleteTempFile("MINMAX"+AUDIO_RECORDER_TEMP_FILE);

		recorder.startRecording();

		isRecording = true;

		threadRecord = new Thread(new Runnable() {

			@Override
			public void run() {
				recordAudioData();
			}
		}, "AudioTime+ Record Thread");

		threadRecord.start();
	}

	public void stopRecording() {
		if (null != recorder) {
			isRecording = false;

			recorder.stop();
			recorder.release();

			recorder = null;
			threadRecord = null;
		}
	}

	private String getTempFilename(String s) {
		String filepath = Environment.getExternalStorageDirectory().getPath();
		File file = new File(filepath, AUDIO_RECORDER_FOLDER);

		if (!file.exists()) {
			file.mkdirs();
		}

		File tempFile = new File(filepath, s);

		if (tempFile.exists())
			tempFile.delete();

		return (file.getAbsolutePath() + "/" + s);
	}

	private void deleteTempFile(String s) {
		File file = new File(getTempFilename(s));

		file.delete();
	}

	private void cleardBPlot() {
		dBPlot.clear();
		dBPlot.setDomainStep(XYStepMode.INCREMENT_BY_VAL, 1);
		dBPlot.setTitle(getString(R.string.app_name));

		clearMarkers();
		dBSeries = null;
		dBSeries = new SimpleXYSeries(getString(R.string.range_label));

		dBPlot.setDomainBoundaries(0, INITIAL_DOMAIN_SIZE, BoundaryMode.FIXED);
		redrawPlot();
	}

	private void recordAudioData() {
		byte data[] = new byte[bufferSize];
		byte yValue[]=new byte[2];
		BufferedOutputStream osRAW = null;
		BufferedOutputStream osMINMAX = null;
		int y, minY=Integer.MAX_VALUE, maxY=-Integer.MAX_VALUE;
		double minYtime=0, maxYtime=0;
		int read = 0, totalRead = 0;
		long runningCount=0;
		double x = 0;

		try {
			osRAW = new BufferedOutputStream(new FileOutputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
			osMINMAX = new BufferedOutputStream(new FileOutputStream(getTempFilename("MINMAX"+AUDIO_RECORDER_TEMP_FILE)));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		dBPlot.setDomainBoundaries(0, INITIAL_DOMAIN_SIZE, BoundaryMode.FIXED);
		
		while (isRecording) { 
			read = recorder.read(data, 0, bufferSize);

			if (read != AudioRecord.ERROR_INVALID_OPERATION) {
				try {
					osRAW.write(data, 0, read);
				} catch (IOException e) {
					e.printStackTrace();
				}

				int i = 0;
				while (i < read) {
					y = (int) ((data[i + 1] << 8) | data[i]);
					
					if(y<minY) {
						minY=y;
						minYtime=x;
					}
					if(y>maxY) {
						maxY=y;
						maxYtime=x;
					}
					i=i+2;
					runningCount = runningCount + 2;
					
					if(runningCount % SAMPLES_PER_ONEHUNDREDTH_SECOND == 0) 															// SAMPLES_PER_ONEHUNDREDTH_SECOND samples = .01s 
					  try {
						if( minYtime < maxYtime) {  
							dBSeries.addLast(minYtime, (float) minY);						
							dBSeries.addLast(maxYtime, (float) maxY);
							
							yValue[0] = (byte)(minY & 0xff);
							yValue[1] = (byte)((minY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
							
							yValue[0] = (byte)(maxY & 0xff);
							yValue[1] = (byte)((maxY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
						}
						else { 
							dBSeries.addLast(maxYtime, (float) maxY);
							dBSeries.addLast(minYtime, (float) minY);
							
							yValue[0] = (byte)(maxY & 0xff);
							yValue[1] = (byte)((maxY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
							
							yValue[0] = (byte)(minY & 0xff);
							yValue[1] = (byte)((minY & 0xff00) >> 8);
							osMINMAX.write(yValue, 0, 2);
						}	
						if (x > INITIAL_DOMAIN_SIZE) {
							dBSeries.removeFirst();
							dBSeries.removeFirst();
						}
						minY=Integer.MAX_VALUE;
						maxY=-Integer.MAX_VALUE;
					  } catch (IOException e) {
						  e.printStackTrace();
					  }
					x = x + ONESAMPLETIME;
				}
				dBPlot.addSeries(dBSeries, markedFormatter);
				if (x > INITIAL_DOMAIN_SIZE) 
					dBPlot.setDomainBoundaries(dBSeries.getX(0), x, BoundaryMode.FIXED); 

				redrawPlot();
				totalRead = totalRead + read;
			}
		}

		try {
			osRAW.close();
			osMINMAX.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

		dBPlot.clear();
		dBPlot.addSeries(dBSeries, markedFormatter);

		minXY = new PointF(0, -32768); 
		maxXY = new PointF((totalRead / ((float) RECORDER_SAMPLERATE * 2)), 32767); 
		maxX = maxXY.x;

		reloaddBSeries();
	}

	private void startReloadThread(){
		threadReload = new Thread(new Runnable() {

		@Override
		public void run() {
				reload();
			}
		}, "AudioTime+ Reload Thread");

		threadReload.start();
	}
	
	private void reloaddBSeries() {
		long currentTime=System.currentTimeMillis();
		if(currentTime-lastTime < ELAPSEDTIME) return;							// Only reload when visually necessary
		lastTime=currentTime;
		long samplesAvailable = (long) (RECORDER_SAMPLERATE * (maxXY.x - minXY.x));
		if (samplesAvailable <= 1) return; 										// Nothing to do

		isReloading = true;
		synchronized(dBPlot) {
			dBPlot.notifyAll();
		}
	}

	private void reload() {
	/* Reloads data from one of two files and generates plot
	 * 
	 *  Due to the large number of samples recorded, 4 cases are used to determine how much data should be displayed. 
	 *  Global variables minXY.x and maxXY.x determine the window of data samples to display.
	 *  
	 *  The cases, from smallest number of samples in window to largest are:
	 *  
	 *   1) number data samples <= SERIES_SIZE, all data is displayed by reading AUDIO_RECORDER_TEMP_FILE
	 *   2) SERIES_SIZE < number data samples < 5s of data samples, the min/max values over an interval of (maxXY.x - minXY.x) / SERIES_SIZE are displayed
	 *   3) 5s < number data samples < 2205s, compressed min/max values are read from "MINMAX"+AUDIO_RECORDER_TEMP_FILE and the min/max of those values over an interval of (maxXY.x - minXY.x) / SERIES_SIZE are displayed
	 *   4) 2205s < number data samples, a single sample from the interval (maxXY.x - minXY.x) / (SERIES_SIZE*5) is displayed from AUDIO_RECORDER_TEMP_FILE
	 *   
	 *  Displaying min/max values reduces the number of samples while producing reasonable visible correspondence to the actual data.
	 * 
	 */
	  final double compressionX = SAMPLES_PER_ONEHUNDREDTH_SECOND/2.0;											// 2 MIN/MAX samples were recorded for every SAMPLES_PER_ONEHUNDREDTH_SECOND 
	  	  
	  BufferedInputStream in = null;
	  byte[] data = new byte[2];
	  	
	  while(true)
		synchronized(dBPlot){ 
			while(!isReloading)	
				try {
					dBPlot.wait();
				} catch (InterruptedException e) {}
			
			dBPlot.clear();
			long samplesAvailable = (long) (RECORDER_SAMPLERATE * (maxXY.x - minXY.x));
			long samplesToRead = Math.min(samplesAvailable, SERIES_SIZE);

			double xStep = 0;
			double x = minXY.x;
			long samplesRead = 0;
			float xMarkLeft=0f, xMarkRight=0f;
			int y;
			
			dBSeries = new SimpleXYSeries(getString(R.string.range_label));
			
			if (markerLeft != null)
				xMarkLeft = markerLeft.getValue().floatValue();
			if (markerRight != null)
				xMarkRight = markerRight.getValue().floatValue();
			
			if(maxXY.x-minXY.x > 5.0 && maxXY.x-minXY.x < 2205.0 ) {									// Case 3: Display window size 5s to 2205s
				try {																					// Process SAMPLES_PER_ONEHUNDREDTH_SECOND to 1 compression (100/s) min/max values 
					in = new BufferedInputStream(new FileInputStream(getTempFilename("MINMAX"+AUDIO_RECORDER_TEMP_FILE)));
					in.skip((int) (minXY.x * 200) * 2); 												// Skip 2 bytes/sample, sampled at 100/s
					
					int minY, maxY;
					double minYtime=x, maxYtime=x;
					boolean eof = false;
					boolean min, max;
					double deltaX=0;
					double incrementX = ONESAMPLETIME*compressionX;
					
					xStep = (maxXY.x - minXY.x) / SERIES_SIZE;
					
					while (!eof && x < maxXY.x) {
						minY=Integer.MAX_VALUE;
						maxY=-Integer.MAX_VALUE;
						minYtime=x;
						maxYtime=x;
						deltaX=0;
						x = x + incrementX;
						min = false;
						max = false;

						while (!(eof = (in.read(data, 0, 2) == -1)) && x < maxXY.x && deltaX < xStep) {			// Find min & and max
							y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 	 						
							y = y <= 32767 ? y : y - 65535;
							
							if(y<minY) {
								minY=y;
								minYtime=x;
								min=true;
							}
							if(y>maxY) {
								maxY=y;
								maxYtime=x;
								max=true;
							}
							
							deltaX = deltaX + incrementX;
							x = x + incrementX;
							
							if (Math.abs(xMarkLeft - x) <= incrementX)  								// Force marker <x,y> value into plot
								dBSeries.addLast(xMarkLeft, (float) y);
							else 						
								if (Math.abs(xMarkRight - x) <= incrementX)  							// Force marker <x,y> value into plot
									dBSeries.addLast(xMarkRight, (float) y);									
						}
						
						if(min && max) {
							if( minYtime < maxYtime) {  
								dBSeries.addLast(minYtime, (float) minY);
								dBSeries.addLast(maxYtime, (float) maxY);
							}
							else { 
								dBSeries.addLast(maxYtime, (float) maxY);
								dBSeries.addLast(minYtime, (float) minY);
							}	
						}
					}

					in.close();
				} 
				catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			else {	
				try {
					in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
	
					in.skip((int) (RECORDER_SAMPLERATE * minXY.x) * 2); 									// Skip 2 bytes/sample
	
					if (samplesToRead == SERIES_SIZE) {														
						if(maxXY.x - minXY.x > 5.0) {														// Case 4: Display window over 2205s, plot and skip points
							xStep = (maxXY.x - minXY.x) / (SERIES_SIZE*5);
							int skip=(int)(RECORDER_SAMPLERATE*xStep)*2;
							int bytesRead = (int) (RECORDER_SAMPLERATE * minXY.x) * 2;
	
							while (in.read(data, 0, 2) != -1 && x <= maxXY.x) {								
								y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 							// Little endian
								y = y <= 32767 ? y : y - 65535;
								dBSeries.addLast(x, (float) y);
								bytesRead = bytesRead + 2;
	
								if (xMarkLeft > x && xMarkLeft < x + xStep) { 								// Force marker <x,y> value into plot
									in.close();
									in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
									bytesRead = (int) (RECORDER_SAMPLERATE * xMarkLeft) * 2;
									in.skip(bytesRead); 													// Skip 2 bytes/sample
									x = xMarkLeft;
								} else if (xMarkRight > x && xMarkRight < x + xStep) {
									in.close();
									in = new BufferedInputStream(new FileInputStream(getTempFilename(AUDIO_RECORDER_TEMP_FILE)));
									bytesRead = (int) (RECORDER_SAMPLERATE * xMarkRight) * 2;
									in.skip(bytesRead); 													// Skip 2 bytes/sample
									x = xMarkRight;
								} else {
									x = x + xStep;
									int skipError = (int) (RECORDER_SAMPLERATE * x) * 2 - (bytesRead + skip); // Correction to keep time and audio data synch'ed
									skip = skip + skipError;
									in.skip(skip);
									bytesRead = bytesRead + skip;
								}
							}					
						}
						else {																					// Case 2: Display SERIES_SIZE < window < 5s, plot min/max points
							int minY, maxY;
							double minYtime=x, maxYtime=x;
							boolean eof = false;
							boolean min, max;
							double deltaX=0;
							
							xStep = (maxXY.x - minXY.x) / SERIES_SIZE;
							
							while (!eof && x < maxXY.x) {
								minY=Integer.MAX_VALUE;
								maxY=-Integer.MAX_VALUE;
								minYtime=x;
								maxYtime=x;
								deltaX=0;
								x = x + ONESAMPLETIME;
								min = false;
								max = false;
	
								while (!(eof = (in.read(data, 0, 2) == -1)) && x < maxXY.x && deltaX < xStep) {	// Find min & and max
									y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 	 						
									y = y <= 32767 ? y : y - 65535;
									
									if(y<minY) {
										minY=y;
										minYtime=x;
										min=true;
									}
									if(y>maxY) {
										maxY=y;
										maxYtime=x;
										max=true;
									}
									
									deltaX = deltaX + ONESAMPLETIME;
									x = x + ONESAMPLETIME;
									
									if (Math.abs(xMarkLeft - x) <= ONESAMPLETIME)  								// Force marker <x,y> value into plot
										dBSeries.addLast(xMarkLeft, (float) y);
									else 						
										if (Math.abs(xMarkRight - x) <= ONESAMPLETIME)  						// Force marker <x,y> value into plot
											dBSeries.addLast(xMarkRight, (float) y);									
								}
								
								if(min && max) {
									if( minYtime < maxYtime) {  
										dBSeries.addLast(minYtime, (float) minY);
										dBSeries.addLast(maxYtime, (float) maxY);
									}
									else { 
										dBSeries.addLast(maxYtime, (float) maxY);
										dBSeries.addLast(minYtime, (float) minY);
									}	
								}
							}
						}
					} else { 																					// Case 1: Display window < SERIES_SIZE, plot every audio data sample
						xStep = (double) (maxXY.x - minXY.x) / samplesToRead;
						while (in.read(data, 0, 2) != -1 && samplesRead <= samplesToRead) {
							y = (data[0] & 0xFF) | ((data[1] & 0xFF) << 8); 									// Little endian
							y = y <= 32767 ? y : y - 65535;
							dBSeries.addLast(x, y);
							samplesRead++;
							x = x + xStep;
						}
					}
	
					in.close();
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
	
			dBPlot.addSeries(dBSeries, markedFormatter);
			dBPlot.setDomainBoundaries(minXY.x, maxXY.x, BoundaryMode.FIXED);
			dBPlot.setDomainStep(XYStepMode.INCREMENT_BY_VAL, (maxXY.x - minXY.x) / 5);
			
			isReloading = false;
		}
	}
	
	private void startRedrawThread(){
		threadRedraw = new Thread(new Runnable() {

		@Override
		public void run() {
				redraw();
			}
		}, "AudioTime+ Redraw Thread");

		threadRedraw.start();
	}
	
	private void redrawPlot() {
		isDrawing = true;
		synchronized(dBPlot) {
			dBPlot.notifyAll();
		}
	}

	private void redraw() {
		  while(true)
				synchronized(dBPlot){ 
					while(!isDrawing)	
						try {
							dBPlot.wait();
						} catch (InterruptedException e) {}		
					dBPlot.redraw();
					isDrawing = false;
				}
	}
	
	final protected static char[] hexArray = "0123456789ABCDEF".toCharArray();
	public static String bytesToHex(byte[] bytes) {
	    char[] hexChars = new char[bytes.length * 2];
	    int v;
	    for ( int j = 0; j < bytes.length; j++ ) {
	        v = bytes[j] & 0xFF;
	        hexChars[j * 2] = hexArray[v >>> 4];
	        hexChars[j * 2 + 1] = hexArray[v & 0x0F];
	    }
	    return new String(hexChars);
	}

	private void zoom(float scale) {
		float domainSpan = maxXY.x - minXY.x;
		float domainMidPoint = maxXY.x - domainSpan / 2.0f;
		float offset = domainSpan * scale / 2.0f;
		float leftBoundary = 0f; 		
		float rightBoundary = maxX; 	

		minXY.x = domainMidPoint - offset;
		maxXY.x = domainMidPoint + offset;

		if (minXY.x < leftBoundary)
			minXY.x = leftBoundary;
		if (maxXY.x > rightBoundary)
			maxXY.x = rightBoundary;
	}

	private void scroll(float pan) {
		float domainSpan = maxXY.x - minXY.x;
		float step = domainSpan / dBPlot.getWidth();
		float offset = pan * step;
		float leftBoundary = 0f; 
		float rightBoundary = maxX; 

		minXY.x = minXY.x + offset;
		maxXY.x = maxXY.x + offset;

		if (minXY.x < leftBoundary) {
			minXY.x = leftBoundary;
			maxXY.x = leftBoundary + domainSpan;
		} else if (maxXY.x > rightBoundary) {
			maxXY.x = rightBoundary;
			minXY.x = rightBoundary - domainSpan;
		}
	}

	private float spacing(MotionEvent event) {
		float x = event.getX(0) - event.getX(1);
		float y = event.getY(0) - event.getY(1);
		return (float) Math.sqrt(x * x + y * y);
	}

	@Override
	public boolean onTouchEvent(MotionEvent event) {
		if (maxXY.x == 0.0 || event.getY() > dBPlot.getBottom() )
			return super.onTouchEvent(event); 								// Ignore stray touches outside plot area or touches before recording
		detector.onTouchEvent(event);

		switch (event.getAction() & MotionEvent.ACTION_MASK) {
		case MotionEvent.ACTION_DOWN: 
			markerAdjusted = null;
			if (markerLeft != null
					&& Math.abs(ValPixConverter.valToPix(markerLeft.getValue()
							.doubleValue(), minXY.x, maxXY.x,
							dBPlot.getWidth(), false)
							- event.getX()) < 40)
				markerAdjusted = markerLeft;
			if (markerRight != null
					&& Math.abs(ValPixConverter.valToPix(markerRight.getValue()
							.doubleValue(), minXY.x, maxXY.x,
							dBPlot.getWidth(), false)
							- event.getX()) < 40)
				markerAdjusted = markerRight;
			if (markerAdjusted != null) {
				markerAdjusted.getLinePaint().setColor(Color.BLUE);
				markerAdjusted.getTextPaint().setColor(Color.BLUE);
				redrawPlot();
				mode = ONE_FINGER_ADJUST;
				break;
			}
			firstFinger = new PointF(event.getX(), event.getY());
			mode = ONE_FINGER_DRAG;
			break;
		case MotionEvent.ACTION_UP:
		case MotionEvent.ACTION_POINTER_UP:
			if (markerAdjusted != null) {
				markerAdjusted.getLinePaint().setColor(Color.YELLOW);
				markerAdjusted.getTextPaint().setColor(Color.YELLOW);
			}
			redrawPlot();
			mode = NONE;
			break;
		case MotionEvent.ACTION_POINTER_DOWN: 								// second finger
			distBetweenFingers = spacing(event);							// the distance check is done to avoid false alarms
			if (distBetweenFingers > 5f) {
				mode = TWO_FINGERS_DRAG;
			}
			break;
		case MotionEvent.ACTION_MOVE:
			if (mode == ONE_FINGER_ADJUST && markerLeft != null && markerRight != null) {
				removeMarkers();
				if (markerLeft != null
						&& Math.abs(ValPixConverter.valToPix(markerLeft
								.getValue().doubleValue(), minXY.x, maxXY.x,
								dBPlot.getWidth(), false)
								- event.getX()) < 40) 
					markerAdjusted = markerLeft;
				if (markerRight != null
						&& Math.abs(ValPixConverter.valToPix(markerRight
								.getValue().doubleValue(), minXY.x, maxXY.x,
								dBPlot.getWidth(), false)
								- event.getX()) < 40)
					markerAdjusted = markerRight;
				if (markerAdjusted == markerLeft) {
					markerLeft = markerAtX(pixelToValueX(event.getX()), Color.BLUE);
					markerRight = markerAtX(markerRight.getValue(), Color.YELLOW);
					markerAdjusted = markerLeft;
				}
				if (markerAdjusted == markerRight) {
					markerRight = markerAtX(pixelToValueX(event.getX()), Color.BLUE);
					markerLeft = markerAtX(markerLeft.getValue(), Color.YELLOW);
					markerAdjusted = markerRight;
				}
				addMarkedRegion();
				redrawPlot();
			} else if (mode == ONE_FINGER_ADJUST && markerLeft != null) {
				removeMarkers();
				markerAdjusted = markerLeft;
				markerLeft = markerAtX(pixelToValueX(event.getX()), Color.BLUE);
				markerAdjusted = markerLeft;
				correctMarkers();
				redrawPlot();
			} else if (mode == ONE_FINGER_DRAG) {
				PointF oldFirstFinger = firstFinger;
				firstFinger = new PointF(event.getX(), event.getY());
				if (Math.abs(oldFirstFinger.x - firstFinger.x) > 0) {
					scroll(oldFirstFinger.x - firstFinger.x);
					reloaddBSeries();
					correctMarkers();
					redrawPlot();
				}
			} else if (mode == TWO_FINGERS_DRAG) {
				float oldDist = distBetweenFingers;
				distBetweenFingers = spacing(event);
				zoom(oldDist / distBetweenFingers);
				reloaddBSeries();
				correctMarkers();
				redrawPlot();
			}
			break;
		}

		return super.onTouchEvent(event);
	}

	private void correctMarkers() {
		if (isMarkerOffGraph(markerLeft))
			dBPlot.removeMarker(markerLeft);

		if (isMarkerOnGraph(markerLeft))
			dBPlot.addMarker(markerLeft);

		if (isMarkerOffGraph(markerRight))
			dBPlot.removeMarker(markerRight);

		if (isMarkerOnGraph(markerRight))
			dBPlot.addMarker(markerRight);
	}

	private boolean isMarkerOffGraph(XValueMarker m) {
		if (m == null)
			return false;
		return m.getValue().floatValue() < minXY.x
				|| m.getValue().floatValue() > maxXY.x;
	}

	private boolean isMarkerOnGraph(XValueMarker m) {
		if (m == null)
			return false;
		return m.getValue().floatValue() > minXY.x
				&& m.getValue().floatValue() < maxXY.x;
	}

/*	private float pixelToValueY(float y) {
		// Parameters: 1=input y-value, 2=minimal y-value that is shown,
		// 3=maximal y-value that is shown, 4=Height of the view, 5=flip
		if (y < 0)
			return (float) 0.0;
		return (float) ValPixConverter.pixToVal(y, minXY.y, maxXY.y,
				dBPlot.getHeight(), false);
	}
*/
	private float pixelToValueX(float x) {
		// Parameters: 1=input x-value, 2=minimal x-value that is shown,
		// 3=maximal x-value that is shown, 4=Width of the view, 5=flip
		if (x < 0)
			return (float) 0.0;
		return (float) ValPixConverter.pixToVal(x, minXY.x, maxXY.x,
				dBPlot.getWidth(), false);
	}

	@Override
	public boolean onDown(MotionEvent e) {
		// Log.d("---onDown----", e.toString());
		return false;
	}

	@Override
	public boolean onFling(MotionEvent e1, MotionEvent e2, float velocityX,
			float velocityY) {
//		 Log.d("---onFling---", e1.toString() + e2.toString());
		return false;
	}

	@Override
	public void onLongPress(MotionEvent e) {
		// Log.d("---onLongPress---", e.toString());
	}

	@Override
	public boolean onScroll(MotionEvent e1, MotionEvent e2, float distanceX,
			float distanceY) {
		// Log.d("---onScroll---", e1.toString() + e2.toString());
		return false;
	}

	@Override
	public void onShowPress(MotionEvent e) {
		// Log.d("---onShowPress---", e.toString());
	}

	@Override
	public boolean onSingleTapUp(MotionEvent e) {
//		 Log.d("---onSingleTapUp---", e.toString());
		return false;
	}

	@Override
	public boolean onDoubleTap(MotionEvent e) {
		// Log.d("---onDoubleTap---", e.toString());
		clearMarkers();
		return false;
	}

	@Override
	public boolean onDoubleTapEvent(MotionEvent e) {
		// Log.d("---onDoubleTapEvent---", e.toString());
		return false;
	}

	@Override
	public boolean onSingleTapConfirmed(MotionEvent e) {
		if (maxXY.x == 0.0)
			return false; // Stray touch before any recording
		mode = NONE;

		if (markerLeft != null && markerRight != null)
			return false;

		XValueMarker marker = markerAtX(pixelToValueX(e.getX()), Color.YELLOW);

		if (markerLeft == null && markerRight == null) {
			markerLeft = marker;
			return false;
		}
		if (marker.getValue().floatValue() > markerLeft.getValue().floatValue())
			markerRight = marker;
		else {
			markerRight = markerLeft;
			markerLeft = marker;
		}

		addMarkedRegion();
		return false;
	}

	private void addMarkedRegion() {
		markedRegionFormatter = new XYRegionFormatter(Color.YELLOW);
		markedRegionFormatter.getPaint().setAlpha(100);
		
		markedRegion = new RectRegion(markerLeft.getValue(), markerRight.getValue(), Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, 
						" " + getString(R.string.interval_label) + " " + (markerRight.getValue().floatValue() - markerLeft.getValue().floatValue()));
		markedFormatter.addRegion(markedRegion, markedRegionFormatter);
	}

	private void clearMarkers() {
		removeMarkers();
		markerLeft = null;
		markerRight = null;
	}

	private void removeMarkers() {
		dBPlot.removeXMarkers();
		if (markedFormatter == null || markedRegion == null
				|| markedRegionFormatter == null)
			return;
		markedFormatter.removeRegion(markedRegion);
//		redrawPlot();
		dBPlot.redraw();														// Direct redraw without synchronized dBPlot access													
	}

	private XValueMarker markerAtX(Number xVal, int color) {
		XValueMarker xMarker = new XValueMarker(xVal, // xVal to mark
				"" + (int) (10000 * xVal.floatValue()) / 10000.0, // marker label to 4 decimal digits
				new YPositionMetric( // object instance to set text positioning on the marker
						PixelUtils.dpToPix(5), // 5dp offset
						YLayoutStyle.ABSOLUTE_FROM_TOP), // offset origin
				color, // line paint color
				color); // text paint color

		xMarker.getTextPaint().setTextSize(PixelUtils.dpToPix(14));

		DashPathEffect dpe = new DashPathEffect(new float[] {
				PixelUtils.dpToPix(2), PixelUtils.dpToPix(2) }, 0);

		xMarker.getLinePaint().setPathEffect(dpe);
		xMarker.setTextOrientation(ValueMarker.TextOrientation.VERTICAL);

		dBPlot.addMarker(xMarker);
//		redrawPlot();
		dBPlot.redraw();														// Direct redraw without synchronized dBPlot access
		return xMarker;
	}
	
}