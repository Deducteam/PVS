package com.sri.csl.pvs.plugin.handlers;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.Launch;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.console.IOConsoleOutputStream;
import org.eclipse.ui.handlers.HandlerUtil;
import org.json.JSONObject;

import com.sri.csl.pvs.PVSExecutionManager;
import com.sri.csl.pvs.PVSExecutionManager.PVSRespondListener;
import com.sri.csl.pvs.PVSJsonWrapper;
import com.sri.csl.pvs.plugin.Activator;
import com.sri.csl.pvs.plugin.run.IOConsoleKeyboardReader;
import com.sri.csl.pvs.plugin.run.PVSConsole;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class StartPVSHandler extends AbstractHandler {
	private IOConsoleKeyboardReader keyboardReader;
	private IWorkbenchWindow window;
	
	/**
	 * The constructor.
	 */
	public StartPVSHandler() {
	}

	/**
	 * the command has been executed, so extract extract the needed information
	 * from the application context.
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
		if ( PVSExecutionManager.isPVSRunning() ) {
			MessageDialog.openInformation(window.getShell(), "PVS Running", "An instance of PVS is already running.");
		} else {
			try {
				final PVSConsole console = PVSConsole.getConsole();
				console.activate();
				console.clearConsole();
				final IOConsoleOutputStream outStream = console.newOutputStream();
				Map<String, String> attributes = new HashMap<String, String>();
				attributes.put(IProcess.ATTR_CMDLINE, PVSExecutionManager.getPVSStartingCommand());
				ILaunch launch = new Launch(null, ILaunchManager.RUN_MODE, null);
				IProcess process = DebugPlugin.newProcess(launch, PVSExecutionManager.startPVS(), Activator.name, attributes);
				DebugPlugin.getDefault().getLaunchManager().addLaunch(launch);
				PVSJsonWrapper.init();
				PVSExecutionManager.addListener(new PVSRespondListener() {

					@Override
					public void onMessageReceived(String message) {
						try {
							outStream.write(message);
						} catch (IOException e) {
							e.printStackTrace();
						}
					}

					@Override
					public void onMessageReceived(JSONObject message) {
						System.out.println("JSON received: " + message);
						// Do nothing for JSON messages.
					}
					
				});				
				IStreamsProxy streamProxy = process.getStreamsProxy();
				IStreamMonitor outMonitor = streamProxy.getOutputStreamMonitor();
				outMonitor.addListener(new IStreamListener() {
					public void streamAppended(String text, IStreamMonitor monitor) {
						PVSExecutionManager.dispatchMessage(text);
					}				
				});
				
				keyboardReader = new IOConsoleKeyboardReader(console);
				keyboardReader.addListener(new IOConsoleKeyboardReader.IOConsoleKeyboardReaderListener() {
					public void onTextReceived(String text) {
						PVSExecutionManager.writeToPVS(text);
					}
				});
				keyboardReader.start();
				
				
			} catch (IOException e) {
				MessageDialog.openInformation(window.getShell(), "Error", "Failed to start PVS");
			}
		}
		return null;
	}
}
