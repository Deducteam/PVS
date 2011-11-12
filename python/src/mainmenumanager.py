
# This class manages all the menu items in the main menu of the editor

import wx
from constants import *
from eventhandler import *
import config

log = config.getLogger(__name__)

class MainFrameMenu(wx.MenuBar):
    def __init__(self):
        wx.MenuBar.__init__(self)
        self.addFileMenu()
        self.addEditMenu()
        self.addViewMenu()
        self.addPVSMenu()
        self.setBindings()
        
    def addFileMenu(self):
        fileMenu = wx.Menu()
        self.newFileMenuItem = fileMenu.Append(wx.ID_NEW, LABEL_NEW + DOTDOTDOT + "\tCtrl-N", EMPTY_STRING, wx.ITEM_NORMAL)
        self.openFileMenuItem = fileMenu.Append(wx.ID_OPEN, LABEL_OPEN + DOTDOTDOT + "\tCtrl-O", EMPTY_STRING, wx.ITEM_NORMAL)
        self.saveFileMenuItem = fileMenu.Append(wx.ID_SAVE, LABEL_SAVE + "\tCtrl-S", EMPTY_STRING, wx.ITEM_NORMAL)
        self.saveFileAsMenuItem = fileMenu.Append(wx.ID_SAVEAS, LABEL_SAVEAS + DOTDOTDOT, EMPTY_STRING, wx.ITEM_NORMAL)
        self.closeFileMenuItem = fileMenu.Append(wx.ID_CLOSE, LABEL_CLOSEFILE + "\tCtrl-W", EMPTY_STRING, wx.ITEM_NORMAL)
        fileMenu.AppendSeparator()
        self.quitMenuItem = fileMenu.Append(wx.ID_EXIT, LABEL_QUIT + "\tCtrl-Q", EMPTY_STRING, wx.ITEM_NORMAL)
        self.Append(fileMenu, LABEL_FILE)
 
    def addEditMenu(self):
        editMenu = wx.Menu()
        self.undoMenuItem = editMenu.Append(wx.ID_UNDO, LABEL_UNDO + "\tCtrl-Z", EMPTY_STRING, wx.ITEM_NORMAL)
        editMenu.AppendSeparator()
        self.cutMenuItem = editMenu.Append(wx.ID_CUT, LABEL_CUT + "\tCtrl-X", EMPTY_STRING, wx.ITEM_NORMAL)
        self.copyMenuItem = editMenu.Append(wx.ID_COPY, LABEL_COPY + "\tCtrl-C", EMPTY_STRING, wx.ITEM_NORMAL)
        self.pasteMenuItem = editMenu.Append(wx.ID_PASTE, LABEL_PASTE + "\tCtrl-V", EMPTY_STRING, wx.ITEM_NORMAL)
        self.selectAllMenuItem = editMenu.Append(wx.ID_SELECTALL, LABEL_SELECTALL + "\tCtrl-A", EMPTY_STRING, wx.ITEM_NORMAL)
        editMenu.AppendSeparator()
        self.findMenuItem = editMenu.Append(wx.ID_FIND, LABEL_FIND + "\tCtrl-F", EMPTY_STRING, wx.ITEM_NORMAL)
        self.Append(editMenu, LABEL_EDIT)

    def addViewMenu(self):
        viewMenu = wx.Menu()
        self.filesAndBuffersTrees = viewMenu.Append(wx.ID_ANY, "Files and Buffers Trees", EMPTY_STRING, wx.ITEM_CHECK)
        viewMenu.Check(self.filesAndBuffersTrees.GetId(), config.preference.visibleFilesBuffersTrees())
        self.proofTree = viewMenu.Append(wx.ID_ANY, "Proof Tree", EMPTY_STRING, wx.ITEM_CHECK)
        viewMenu.Check(self.proofTree.GetId(), config.preference.visibleProofTree())
        self.Append(viewMenu, LABEL_VIEW)

    def addPVSMenu(self):
        pvsMenu = wx.Menu()
        self.changeContextMenuItem =  pvsMenu.Append(wx.ID_ANY, "Change Context...", EMPTY_STRING, wx.ITEM_NORMAL)
        self.restoreContextMenuItem = pvsMenu.Append(wx.ID_ANY, "Restore Context Automatically", EMPTY_STRING, wx.ITEM_CHECK)
        pvsMenu.Check(self.restoreContextMenuItem.GetId(), config.preference.restoreContextAutomatically())
        pvsMenu.AppendSeparator()
        self.startPVSMenuItem = pvsMenu.Append(wx.ID_ANY, LABEL_STARTPVS, EMPTY_STRING, wx.ITEM_NORMAL)
        self.typecheckMenuItem = pvsMenu.Append(wx.ID_ANY, LABEL_TYPECHECK, EMPTY_STRING, wx.ITEM_NORMAL)
        pvsMenu.AppendSeparator()
        self.setPVSLocationMenuItem = pvsMenu.Append(wx.ID_ANY, "Set PVS Location...", EMPTY_STRING, wx.ITEM_NORMAL)
        self.Append(pvsMenu, PVS_U)
        
    def setBindings(self):
        config.frame.Bind(wx.EVT_MENU, onCreateNewFile, self.newFileMenuItem)
        config.frame.Bind(wx.EVT_MENU, onOpenFile, self.openFileMenuItem)
        config.frame.Bind(wx.EVT_MENU, onSaveFile, self.saveFileMenuItem)
        config.frame.Bind(wx.EVT_MENU, onSaveAsFile, self.saveFileAsMenuItem)
        config.frame.Bind(wx.EVT_MENU, onCloseFile, self.closeFileMenuItem)
        config.frame.Bind(wx.EVT_MENU, onQuitFrame, self.quitMenuItem)
        config.frame.Bind(wx.EVT_MENU, onUndo, self.undoMenuItem)
        config.frame.Bind(wx.EVT_MENU, onSelectAll, self.selectAllMenuItem)
        config.frame.Bind(wx.EVT_MENU, onCutText, self.cutMenuItem)
        config.frame.Bind(wx.EVT_MENU, onCopyText, self.copyMenuItem)
        config.frame.Bind(wx.EVT_MENU, onPasteText, self.pasteMenuItem)
        config.frame.Bind(wx.EVT_MENU, onFindText, self.findMenuItem)
        
        config.frame.Bind(wx.EVT_MENU, onViewFilesAndBuffersTrees, self.filesAndBuffersTrees)
        config.frame.Bind(wx.EVT_MENU, onViewProofTree, self.proofTree)
        
        config.frame.Bind(wx.EVT_MENU, onChangeContext, self.changeContextMenuItem)
        config.frame.Bind(wx.EVT_MENU, onRestoreContextAutomatically, self.restoreContextMenuItem)
        config.frame.Bind(wx.EVT_MENU, onStartPVS, self.startPVSMenuItem)
        config.frame.Bind(wx.EVT_MENU, onTypecheck, self.typecheckMenuItem)
        config.frame.Bind(wx.EVT_MENU, onSetPVSLocation, self.setPVSLocationMenuItem)
        
    def enableCloseFile(self, value = True):
        self.closeFileMenuItem.Enable(value)

    def enableUndo(self, value = True):
        self.undoMenuItem.Enable(value)

    def enableCut(self, value = True):
        self.cutMenuItem.Enable(value)

    def enableCopy(self, value = True):
        self.copyMenuItem.Enable(value)

    def enablePaste(self, value = True):
        self.pasteMenuItem.Enable(value)

    def enableSelectAll(self, value = True):
        self.selectAllMenuItem.Enable(value)

    def enableFind(self, value = True):
        self.findMenuItem.Enable(value)


