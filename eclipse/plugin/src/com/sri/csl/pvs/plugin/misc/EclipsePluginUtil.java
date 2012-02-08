package com.sri.csl.pvs.plugin.misc;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import com.sri.csl.pvs.plugin.editor.PVSEditor;

public class EclipsePluginUtil {
	public static IEditorPart getVisibleEditor() {
		IWorkbench wb = PlatformUI.getWorkbench();
		IWorkbenchWindow win = wb.getActiveWorkbenchWindow();
		IWorkbenchPage page = win.getActivePage();
		IEditorReference[] editorReferences = page.getEditorReferences();
		for (IEditorReference edRef: editorReferences) {
			IEditorPart ed = edRef.getEditor(false);
			if ( page.isPartVisible(ed) ) {
				return ed;
			}
			
		}
		return null;
	}
	
	public static String getVisiblePVSEditorFilename() {
		String filename = null;
		IEditorPart acEditor = EclipsePluginUtil.getVisibleEditor();
		if ( acEditor instanceof PVSEditor ) {
			filename = ((PVSEditor)acEditor).getFile().getFullPath().toOSString();
		}
		return filename;
	}
	
	public static String selectDirectory(String message) {
		String newL = null;
	    Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		DirectoryDialog dd = new DirectoryDialog(shell);
		dd.setMessage(message);
		newL = dd.open();
		return newL;
	}
	
	public static void showMessage(String message, int type) {
		Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		MessageBox box = new MessageBox(shell, type);
		if ( type == SWT.ICON_ERROR ) 
			box.setText("Error");
		else if ( type == SWT.ICON_WARNING ) 
			box.setText("Warning");
		else 
			box.setText("Message");
		box.setMessage(message);
		box.open();
	}
	
	public static int askUserYesNo(String question) {
		Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		MessageBox box = new MessageBox(shell, SWT.YES | SWT.NO);
		box.setText("Question");
		box.setMessage(question);
		return box.open();
	}
	
	public static int askUserYesNoCancel(String question) {
		Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		MessageBox box = new MessageBox(shell, SWT.YES | SWT.NO | SWT.CANCEL);
		box.setText("Question");
		box.setMessage(question);
		return box.open();
	}
	
	public static int askUserOkCancel(String question) {
		Shell shell = PlatformUI.getWorkbench().getDisplay().getActiveShell();
		MessageBox box = new MessageBox(shell, SWT.OK | SWT.CANCEL);
		box.setText("Question");
		box.setMessage(question);
		return box.open();
	}
	
	
}
