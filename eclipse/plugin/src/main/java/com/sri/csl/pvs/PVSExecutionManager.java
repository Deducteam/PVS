package com.sri.csl.pvs;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.logging.Logger;

import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.json.JSONException;
import org.json.JSONObject;

import com.sri.csl.pvs.plugin.Activator;
import com.sri.csl.pvs.plugin.preferences.PreferenceConstants;

public class PVSExecutionManager {
	protected static Logger log = Logger.getLogger(PVSExecutionManager.class.getName());	
	
	public interface PVSRespondListener {
		public void onMessageReceived(String message);
		public void onMessageReceived(JSONObject message);
	}
	
	protected static ArrayList<PVSRespondListener> listeners = new ArrayList<PVSRespondListener>();
	protected static Process process = null;
	
	protected static String getPVSDirectory() {
		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
		return store.getString(PreferenceConstants.PVSPATH);
	}
	
	public static void addListener(PVSRespondListener l) {
		listeners.add(l);
	} 
	
	public static void removeListener(PVSRespondListener l) {
		listeners.remove(l);
	}
	
	public static String getPVSLocation() {
		return getPVSDirectory() + "/" + "pvs";
	}
	
	public static String getPVSStartingCommand() {
		return getPVSLocation()  + " -raw";
	}
	
	public static String getPVSPromptRegex(int lispType) {
		switch ( lispType ) {
		case 1: // Allegro
			return PVSConstants.pvsAllegroPrompt;
		case 2: // CMU
			return PVSConstants.pvsCmuPrompt;
		}
		return PVSConstants.simplePrompt;
	}
	
	public static Process startPVS() throws IOException {
		if ( (new File(getPVSLocation()).exists()) ) {
			Runtime runtime = Runtime.getRuntime();
			process = runtime.exec(getPVSStartingCommand());
			
		} else {
			Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
			MessageDialog.openError(shell, "PVS Not found", "Please enter the correct path to PVS in the preference page.");
		}
		return process;
	}
	
	public static Process getProcess() {
		return process;
	}
	
	public static void writeToPVS(String message) {
		if ( process != null ) {
			OutputStream st = process.getOutputStream();
			try {
				st.write((message + "\n").getBytes());
				st.flush();
			} catch (IOException e) {
				// e.printStackTrace();
			}
		}
	}
	
	public static boolean isPVSRunning() {
		ILaunchManager manager = DebugPlugin.getDefault().getLaunchManager();
		IProcess[] processes = manager.getProcesses();
		for (IProcess p: processes) {
			if ( Activator.name.equals(p.getLabel()) ) {
				return !p.isTerminated();
			}
		}
		return false;
	}
	
	public static InputStream getInputStream() {
		return process != null? process.getInputStream(): null;
	}

	public static OutputStream getOutputStream() {
		return process != null? process.getOutputStream(): null;
	}

	public static InputStream getErrorStream() {
		return process != null? process.getErrorStream(): null;
	}
	
	public static void dispatchJSONMessage(String message) {
		try {
			JSONObject json = null;
			json = new JSONObject(message);
			for (PVSRespondListener l: listeners) {
				l.onMessageReceived(json);
			}
		} catch (JSONException e) {
			e.printStackTrace();
		}
	}
	
	public static void dispatchStringMessage(String message) {
		for (PVSRespondListener l: listeners) {
			l.onMessageReceived(message);
		}
	}
	
	public static void pvsPromptReceived(String prompt) {
		// Prompts are dispatched just like unstructured messages for now.
		for (PVSRespondListener l: listeners) {
			l.onMessageReceived(prompt);
		}		
	}

	public static void stopPVS() {
		if ( process != null ) {
			process.destroy();
		}
	}	
}
