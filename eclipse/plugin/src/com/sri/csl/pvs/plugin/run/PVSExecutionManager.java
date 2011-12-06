package com.sri.csl.pvs.plugin.run;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import com.sri.csl.pvs.plugin.Activator;
import com.sri.csl.pvs.plugin.preferences.PreferenceConstants;

public class PVSExecutionManager {
	protected Process process = null;
	
	public PVSExecutionManager() {
		process = null;
	}
	
	protected static String getPVSDirectory() {
		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
		return store.getString(PreferenceConstants.P_PATH);
	}
	
	public static String getPVSLocation() {
		return getPVSDirectory() + "/" + "pvs";
	}
	
	public static String getPVSStartingCommand() {
		return getPVSLocation()  + " -raw";
	}
	
	public Process startPVS() throws IOException {
		if ( (new File(getPVSLocation()).exists()) ) {
			Runtime runtime = Runtime.getRuntime();
			process = runtime.exec(getPVSStartingCommand());
		} else {
			Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
			MessageDialog.openError(shell, "PVS Not found", "Please enter the correct path to PVS in the preference page.");
		}
		return process;
	}
	
	public Process getProcess() {
		return process;
	}
	
	public void writeToPVS(String message) {
		if ( process != null ) {
			OutputStream st = process.getOutputStream();
			try {
				st.write((message + "\n").getBytes());
				st.flush();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	public InputStream getInputStream() {
		return process != null? process.getInputStream(): null;
	}

	public OutputStream getOutputStream() {
		return process != null? process.getOutputStream(): null;
	}

	public InputStream getErrorStream() {
		return process != null? process.getErrorStream(): null;
	}

	public void stopPVS() {
		if ( process != null ) {
			process.destroy();
		}
	}	
}
