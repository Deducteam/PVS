#                               -*- Mode: Tcl -*- 
# new-pvs-support.tcl -- 
# Author          : Carl Witty with mods by Sam Owre
# Created On      : Thu Apr 27 02:27:14 1995
# Last Modified By: Sam Owre
# Last Modified On: Thu May  4 19:04:20 1995
# Update Count    : 14
# Status          : Unknown, Use with caution!


wm withdraw .

proc emacs-eval {arg} {
    puts stdout ":pvs-eval $arg :end-pvs-eval"
    gets stdin
}

proc emacs-evaln {arg} {
    puts stdout ":pvs-evaln $arg :end-pvs-evaln"
}

proc pvs-send {arg} {
    emacs-evaln [format {(pvs-send '%s)} $arg]
}

proc pvs-send-and-wait {arg} {
    emacs-eval [format {(pvs-send-and-wait '%s)} $arg]
}

proc create-dag {win} {
    upvar #0 dag-$win dag

    catch {unset dag}
    set dag(items) {}
    bind $win <Destroy> "+delete-all-dag-items $win"
}

proc dag-bind-move {win suffix modifier button update} {
    upvar #0 dag-$win dag

    $win bind dag-item <$modifier-$button> \
	"dag-motion-click $win %x %y {$suffix}"
    $win bind dag-item <$modifier-B$button-Motion> \
	"dag-motion-drag $win %x %y $update"
}

proc dag-motion-click {win x y suffix} {
    upvar #0 dag-$win dag
    global moving

    catch {unset moving}

    set dag(oldX) $x
    set dag(oldY) $y

    set dag(drag_path) $dag(idtotag,[$win find withtag current])

    $win dtag selected
    $win addtag selected withtag $dag(drag_path)$suffix

    foreach id [$win find withtag selected] {
	catch {
	    set moving($dag(idtotag,$id)) 1
	}
    }	
}

proc dag-motion-drag {win x y update} {
    upvar #0 dag-$win dag
    global moving

    set dx [expr $x-$dag(oldX)]
    set dy [expr $y-$dag(oldY)]

    $win move selected $dx $dy
    set dag(oldX) $x
    set dag(oldY) $y

    foreach tag [array names moving] {
	incr dag(topx,$tag) $dx
	incr dag(topy,$tag) $dy
	incr dag(botx,$tag) $dx
	incr dag(boty,$tag) $dy
    }

    update-lines-to $win $dag(drag_path)
    if {$update=={both}} {
	update-lines-from $win $dag(drag_path)
    }
}

proc dag-add-item {win tag succs linetags} {
    upvar #0 dag-$win dag

    # Warning...this isn't updated by deletes.
    set dag(items) [concat $dag(items) $tag]

    set dag(succs,$tag) $succs

    foreach item [$win find withtag $tag] {
	if {![string match *dagline* [$win gettags $item]]} {
	    set dag(idtotag,$item) $tag
	    $win addtag dag-item withtag $item
	}
    }

    set bbox [$win bbox $tag.real]
    set dag(anchor,$tag) [list [expr -[lindex $bbox 0]] \
			      [expr -[lindex $bbox 1]]]

    # Give these initial values (it doesn't matter what)
    set dag(topx,$tag) 0
    set dag(botx,$tag) 0
    set dag(topy,$tag) 0
    set dag(boty,$tag) 0

    foreach s $succs {
	# In my opinion, on the X11R6 server, width 0 lines look better
	# than width 1 lines.
	set lineid \
	    [$win create line 0 0 0 0 \
		 -tags "$s dagline$tag,$s dagline.from$tag dagline.to$s dagline $linetags" \
		 -fill [get-option foreground] \
		 -width 0]
	set dag(linefrom,$lineid) $tag
	set dag(lineto,$lineid) $s
    }
}

proc delete-all-dag-items {win} {
    upvar #0 dag-$win dag

    foreach i [array names dag] {
	if {[string match destroy,* $i]} {
	    eval $dag($i)
	}
    }
}

proc dag-delete-item {win tag suffix} {
    upvar #0 dag-$win dag

    $win delete $tag$suffix
    if {$suffix=={}} {
	if {[info exists dag(destroy,$tag)]} {
	    eval $dag(destroy,$tag)
	}
    }
}

proc dag-add-destroy-cb {win tag cb} {
    upvar #0 dag-$win dag

    if {[info exists dag(destroy,$tag)]} {
	set dag(destroy,$tag) [concat $cb ";" $dag(destroy,$tag)]
    } else {
	set dag(destroy,$tag) $cb
    }
}

proc dag-delete-subtree {win tag {suffix .real}} {
    upvar #0 dag-$win dag

    set succs {}
    catch {set succs $dag(succs,$tag)}

    foreach i $succs {
	dag-delete-subtree $win $i {}
    }
    dag-delete-item $win $tag $suffix
}

proc move-dag-item {win tag x y} {
    upvar #0 dag-$win dag

    set bbox [$win bbox $tag.real]
    set anchor $dag(anchor,$tag)

    set curx [expr [lindex $bbox 0]+[lindex $anchor 0]]
    set cury [expr [lindex $bbox 1]+[lindex $anchor 1]]

    $win move $tag [expr $x-$curx] [expr $y-$cury]

    set dag(topx,$tag) $x
    set dag(topy,$tag) [expr $y-1]

    set dag(botx,$tag) $x
    set dag(boty,$tag) [expr $y+1+[lindex $bbox 3]-[lindex $bbox 1]]

    update-lines-to $win $tag
    update-lines-from $win $tag
}

proc update-lines-to {win tag} {
    foreach id [$win find withtag dagline.to$tag] {
	update-line $win $id
    }
}

proc update-lines-from {win tag} {
    foreach id [$win find withtag dagline.from$tag] {
	update-line $win $id
    }
}

proc update-line {win id} {
    upvar #0 dag-$win dag

    $win coords $id \
	$dag(botx,$dag(linefrom,$id)) \
	$dag(boty,$dag(linefrom,$id)) \
	$dag(topx,$dag(lineto,$id)) \
	$dag(topy,$dag(lineto,$id))
}

proc dag-layout {win top} {
    upvar #0 dag-$win dag

    set dag(layout) "dag-layout $win $top"

    foreach item $dag(items) {
	set dag(level,$item) 0
    }

    set maxlev 0

    set change 1
    while {$change} {
	set change 0
	foreach item $dag(items) {
	    set lev $dag(level,$item)
	    foreach succ $dag(succs,$item) {
		if {$dag(level,$succ)<=$lev} {
		    set dag(level,$succ) [expr 1+$lev]
		    set change 1
		    if {$lev==$maxlev} {
			incr maxlev
		    }
		}
	    }
	}
    }

    set y 0
    for {set lev 0} {$lev<=$maxlev} {incr lev} {
	set wd -[get-option xSep $win]
	set ht 0
	foreach item $dag(items) {
	    if {$dag(level,$item)==$lev} {
		set bbox [$win bbox $item.real]
		set w [expr [lindex $bbox 2]-[lindex $bbox 0]]
		set h [expr [lindex $bbox 3]-[lindex $bbox 1]]
		incr wd [get-option xSep $win]
		incr wd $w
		if {$h>$ht} {
		    set ht $h
		}
	    }
	}
	set x [expr -int($wd/2)]
	foreach item $dag(items) {
	    if {$dag(level,$item)==$lev} {
		set bbox [$win bbox $item.real]
		set w [expr [lindex $bbox 2]-[lindex $bbox 0]]
		move-dag-item $win $item [expr $x+int($w/2)] $y
		incr x [get-option xSep $win]
		incr x $w
	    }
	}
	incr y [get-option ySep $win]
	incr y $ht
    }	    
}

proc dagwin-layout {win} {
    upvar #0 dag-$win dag

    eval $dag(layout)
    canvas-set-scroll $win 1
}

proc tree-layout {win top} {
    upvar #0 dag-$win dag

    set dag(layout) "tree-layout $win $top"

    update-widths $win $top
    move-tree $win $top
}

proc update-widths {win tag} {
    upvar #0 dag-$win dag

    set bbox [$win bbox $tag.real]
    set width [expr [lindex $bbox 2]-[lindex $bbox 0]]

    set kw -[get-option xSep $win]
    foreach sub $dag(succs,$tag) {
	update-widths $win $sub
	incr kw $dag(width,$sub)
	incr kw [get-option xSep $win]
    }

    set dag(width,$tag) [expr {$kw>$width?$kw:$width}]
}

proc move-tree {win tag {x 0} {y 0}} {
    upvar #0 dag-$win dag

    move-dag-item $win $tag $x $y

    set bbox [$win bbox $tag.real]

    set kw -[get-option xSep $win]
    foreach succ $dag(succs,$tag) {
	incr kw $dag(width,$succ)
	incr kw [get-option xSep $win]
    }

    set curx [expr round($x-$kw/2)]
    foreach succ $dag(succs,$tag) {
	move-tree $win $succ \
	    [expr $curx+$dag(width,$succ)/2] \
	    [expr [get-option ySep $win]+[lindex $bbox 3]]
	incr curx $dag(width,$succ)
	incr curx [get-option xSep $win]
    }
}


# Support for Proof windows

proc ancestors {path top {suffix {}}} {
    if {$path==$top} {
	return $path$suffix
    } else {
	regexp {^(.*)\.([^.]+)$} $path whole pre post
	return [concat $path$suffix [ancestors $pre $top $suffix]]
    }
}

proc kids {path nkids} {
    set kids {}
    for {set i 0} {$i<$nkids} {incr i} {
	lappend kids $path.$i
    }
    return $kids
}

proc delete-proof-subtree {name theory relpath} {
    set proofwin .proof.$theory-$name.fr.c
    set path $theory-$name-$relpath
    catch {move-dag-item $proofwin $path 0 0}

    dag-delete-subtree $proofwin $path
}

proc proof-num-children {name theory path kids} {
    set fullpath $theory-$name-$path
    global $fullpath
    set ${fullpath}(kids) $kids
    catch {unset ${fullpath}(rule)}
    catch {unset ${fullpath}(done)}
    catch {unset ${fullpath}(tcc)}
}

proc proof-rule {name theory path rule} {
    set fullpath $theory-$name-$path
    global $fullpath
    set ${fullpath}(rule) $rule
}

proc proof-sequent {name theory path seqlabel sequent} {
    set fullpath $theory-$name-$path
    global $fullpath
    set ${fullpath}(seqlabel) $seqlabel
    set ${fullpath}(sequent) $sequent
}

proc proof-done {name theory path} {
    set fullpath $theory-$name-$path
    global $fullpath
    set pwin .proof.$theory-$name.fr.c
    set ${fullpath}(done) 1

    my-foreground $pwin $fullpath [get-option doneColor]
}

proc proof-tcc {path} {
    global $path

    set ${path}(tcc) 1
}

proc proof-show {name theory path} {
    global env
    set top $theory-$name-top
    set fullpath $theory-$name-$path
    global $fullpath
    set proofwin .proof.$theory-$name.fr.c
    set seq \
	[$proofwin create bitmap 0 0 \
	     -bitmap @$env(PVSPATH)/wish/sequent.xbm \
	     -tags "$fullpath.sequent $fullpath $fullpath.real sequent [ancestors $fullpath $top .desc]" \
	     -anchor n \
	     -foreground [get-option foreground]]
    if [info exists ${fullpath}(rule)] {
	set bbox [$proofwin bbox $seq]
	set seqbot [lindex $bbox 3]
	set ysep [get-option ySep $proofwin]
	# I don't know why it happens, but sometimes get-option returns {}
	# here.  get-option works fine after this function.
	if {$ysep == {}} {
	    set ysep 20
	}
	set linebot [expr $seqbot+$ysep]
	set rule [set ${fullpath}(rule)]
	set alen [get-option abbrevLen]
	if $alen {
	    if {[string length $rule]>$alen} {
		if {[regexp {^[^ ]* } $rule whole]} {
		    set rule "$whole...)"
		}
	    }
	}
	set ${fullpath}(rule_abbr) $rule
	$proofwin create line 0 $seqbot 0 $linebot \
	    -tags "$fullpath.line $fullpath $fullpath.real [ancestors $fullpath $top .desc]" \
	    -fill [get-option foreground]
	$proofwin create text 0 $linebot -text $rule \
	    -tags "$fullpath.rule $fullpath $fullpath.real rule [ancestors $fullpath $top .desc]" \
	    -anchor n \
	    -fill [get-option foreground]
    }

    dag-add-item $proofwin $fullpath [kids $fullpath [set ${fullpath}(kids)]] [ancestors $fullpath $top .desc]
    dag-add-destroy-cb $proofwin $fullpath "global $fullpath; catch {unset $fullpath}"
    if [info exists ${fullpath}(done)] {
	my-foreground $proofwin $fullpath [get-option doneColor]
    } elseif [info exists ${fullpath}(tcc)] {
	my-foreground $proofwin $fullpath [get-option tccColor]
    }
}

proc get-full-rule {proofwin top} {
    global pathtorlabel
    upvar #0 dag-$proofwin dag

    set path $dag(idtotag,[$proofwin find withtag current])
    global $path

    if {![string compare [set ${path}(rule)] [set ${path}(rule_abbr)]]} {
	return
    }

    for {set label 1} {[winfo exists .rule$label]} {incr label} {
    }

    if [info exists pathtorlabel($path)] {
	set rulelab $pathtorlabel($path)
	if {! [winfo ismapped .rule$rulelab.rule]} {
	    wm deiconify .rule$rulelab.rule
	} else {
	    wm iconify .rule$rulelab.rule
	    wm deiconify .rule$rulelab.rule
	}
 	return
    }
    set pathtorlabel($path) $label

    set rulewin .rule$label.rule
    set bbox [$proofwin bbox $path.rule]
    set x [lindex $bbox 2]
    set y [expr round(([lindex $bbox 1]+[lindex $bbox 3])/2)]
    $proofwin create text $x $y -anchor w \
	-tags "$path $path.rlabel $path.rlabel$label rlabel [ancestors $path $top .desc] rlabel.$label" \
	-text $label
    update-color $proofwin $path $path.rlabel$label
    
    frame .rule$label
    toplevel $rulewin -class Command
    frame $rulewin.fr
    pack $rulewin.fr -expand yes -fill both
    text $rulewin.fr.text -bd 2 -relief raised
    $rulewin.fr.text insert end [set ${path}(rule)]
    set height [lindex [split [$rulewin.fr.text index end] .] 0]
    set wd 0
    for {set i 1} {$i<=$height} {incr i} {
	set linewd [lindex [split [$rulewin.fr.text index "$i.0 lineend"] .] 1]
	if {$linewd>$wd} {set wd $linewd}
    }
    $rulewin.fr.text config -height $height -width $wd -state disabled -wrap none
    pack $rulewin.fr.text -expand yes -fill both
    button $rulewin.dismiss -text Dismiss -command "destroy $rulewin"
    pack $rulewin.dismiss -side left -padx 2 -pady 2
    bind $rulewin <Destroy> "+catch {$proofwin delete $path.rlabel$label}"
    bind $rulewin <Destroy> "+catch {unset pathtorlabel($path)}"
    bind $rulewin <Destroy> "+after 1 {catch {destroy .rule$label}}"
    wm iconname $rulewin {PVS command}
    wm title $rulewin "Command $label [set ${path}(rule_abbr)]"

    set next [lindex [set dag(succs,$path)] 0]
    dag-add-destroy-cb $proofwin $next "catch {destroy $rulewin}"
}
    

# proc get-current-sequent {proofwin} {
#     upvar #0 dag-$proofwin dag
# 
#     set path $dag(idtotag,[$proofwin find withtag current])
# 
#     set lisp_path [path-to-lisp-path $path]
# 
#     set file [lindex [pvs-send-and-wait "(request-sequent '($lisp_path))"] 0]
#     source $file
#     exec rm -f $file
# }

proc show-sequent {proofwin top} {    
    global pathtolabel
    upvar #0 dag-$proofwin dag

    set path $dag(idtotag,[$proofwin find withtag current])
    global $path
    set seq_label [set ${path}(seqlabel)]
    set text [set ${path}(sequent)]

    for {set label 1} {[winfo exists .sequent$label]} {incr label} {
    }

    if [info exists pathtolabel($path)] {
	set seqlab $pathtolabel($path)
	if {! [winfo ismapped .sequent$seqlab.sequent]} {
	    wm deiconify .sequent$seqlab.sequent
	} else {
	    wm iconify .sequent$seqlab.sequent
	    wm deiconify .sequent$seqlab.sequent
	}
	return
    }

    set seqwin .sequent$label.sequent
    set bbox [$proofwin bbox $path.sequent]
    set x [lindex $bbox 2]
    set y [expr round(([lindex $bbox 1]+[lindex $bbox 3])/2)]

    $proofwin create text $x $y -anchor w \
	-tags "$path $path.label $path.label$label label [ancestors $path $top .desc] label.$label" \
	-text $label
    update-color $proofwin $path $path.label$label
    
    frame .sequent$label
    toplevel $seqwin -class Sequent -borderwidth 2
    frame $seqwin.fr
    pack $seqwin.fr -expand yes -fill both
    text $seqwin.fr.text -bd 2 -relief raised -height 2 -width 80 -setgrid true
    set text [string range $text 1 [expr [string length $text]-2]]
    $seqwin.fr.text insert end $text
    set height [lindex [split [$seqwin.fr.text index end] .] 0]
    $seqwin.fr.text config -state disabled
    if {$height>5} {
	scrollbar $seqwin.fr.s -command "$seqwin.fr.text yview"
	$seqwin.fr.text config -yscrollcommand "$seqwin.fr.s set"
	pack $seqwin.fr.s -fill y -side right
	wm minsize $seqwin 80 2
	wm maxsize $seqwin 80 $height
	if {$height>[get-option maxHeight]} {
	    set height [get-option maxHeight]
	}
    } else {
	wm minsize $seqwin 80 $height
	wm maxsize $seqwin 80 $height
    }
    pack $seqwin.fr.text -expand yes -fill both
    button $seqwin.dismiss -text Dismiss -command "destroy .sequent$label"
    pack $seqwin.dismiss -side left -padx 2 -pady 2
    button $seqwin.stick -text Stick -command "stick $seqwin $path"
    pack $seqwin.stick -side left -padx 2 -pady 2
    bind $seqwin <Destroy> "catch {$proofwin delete $path.label$label}"
    bind $seqwin <Destroy> "+catch {unset pathtolabel($path)}"
    bind $seqwin <Destroy> "+after 1 {destroy-sequent $seqwin}"
    wm geometry $seqwin 80x$height
    wm iconname $seqwin {PVS sequent}
    wm title $seqwin "Sequent $label ($seq_label)"

    catch {unset sticky_seqs($seqwin)}
    dag-add-destroy-cb $proofwin $path "destroy-sequent $seqwin"
    set pathtolabel($path) $label
}

proc stick {win path} {
    global sticky_seqs $win pathtolabel
    catch {unset pathtolabel($path)}
    set sticky_seqs($win) 1
    pack forget $win.stick
}

proc destroy-sequent {win} {
    global sticky_seqs $win
    if {! [info exists sticky_seqs($win)]} {
	if {[winfo exists $win]} {
	    catch {destroy [winfo parent $win]}
	}
    }
}

proc path-to-lisp-path {path} {
    lrange [split $path .] 1 end
}

proc my-foreground {win tag color} {
    if {[string match @* $color]} {
	if {![string match */* $color]} {
	    global env
	    set color @$env(PVSPATH)/wish/[string range $color 1 end].xbm
	}
	my-config $win line $tag -fill black
	my-config $win line $tag -stipple $color
	my-config $win text $tag -fill black
	my-config $win text $tag -stipple $color
    } else {
	my-config $win bitmap $tag -foreground $color
	my-config $win line $tag -stipple {}
	my-config $win line $tag -fill $color
	my-config $win text $tag -stipple {}
	my-config $win text $tag -fill $color
    }
}

proc update-color {proofwin path tag} {
    global $path curpath

    if [info exists ${path}(done)] {
	my-foreground $proofwin $tag [get-option doneColor]
	return
    }

    if {[info exists curpath]} {
	if {$path==$curpath} {
	    my-foreground $proofwin $tag [get-option currentColor]
	    $proofwin addtag current-subgoal withtag $tag
	    return
	}
    }

    set seqid [$proofwin find withtag $path.sequent]
    set tags [$proofwin gettags $seqid]
    foreach t $tags {
	if {$t=={current-subgoal}} {
	    my-foreground $proofwin $tag [get-option ancestorColor]
	    $proofwin addtag current-subgoal withtag $tag
	    return
	}
    }

    if [info exists ${path}(tcc)] {
	my-foreground $proofwin $tag [get-option tccColor]
	return
    }
    
    my-foreground $proofwin $tag [get-option foreground]
}


proc my-config {win type tag opt val} {
    foreach id [$win find withtag $tag] {
	if {[$win type $id]==$type} {
	    $win itemconfig $id $opt $val
	}
    }
}

proc layout-proof {name theory} {
    set proofwin .proof.$theory-$name.fr.c
    set top $theory-$name-top
    tree-layout $proofwin $top
    canvas-set-scroll $proofwin
}

proc canvas-set-scroll {win {recenter 0}} {
    set allbbox [$win bbox all]
    set allbbox [lreplace $allbbox 1 1 [expr [lindex $allbbox 1]-10]]
    set allbbox [lreplace $allbbox 3 3 [expr [lindex $allbbox 3]+10]]
    $win config -scrollregion $allbbox
    update idletasks
    set winwid [winfo width $win]
    set bboxwid [expr [lindex $allbbox 2]-[lindex $allbbox 0]]
    set margin [expr ($winwid-$bboxwid)/2]
    if {$recenter} {
	$win xview [expr -$margin / [lindex [$win config -scrollincrement] 4]]
    }
}

proc proof-current {name theory relpath} {
    global curpath
    set proofwin .proof.$theory-$name.fr.c
    set top $theory-$name-top
    set path $theory-$name-$relpath

    if {[info exists curpath]} {
	$proofwin delete current-circle
	$proofwin dtag current-subgoal
	set ancs [ancestors $curpath $top]
	unset curpath
	foreach tag $ancs {
	    update-color $proofwin $tag $tag
	}
    }
    if {$relpath!={}} {
	foreach tag [ancestors $path $top] {
	    $proofwin addtag current-subgoal withtag $tag
	}
	my-foreground $proofwin current-subgoal [get-option ancestorColor]
	my-foreground $proofwin $path [get-option currentColor]

	set bbox [$proofwin bbox $path.real]
	regexp {^(.*).c} $proofwin whole fr
	set hscroll $fr.bottom.hscroll
	set vscroll $fr.vscroll

	set hget [$hscroll get]
	set vget [$vscroll get]

	set units [lindex [$proofwin config -scrollincrement] 4]

	set allbbox [lindex [$proofwin config -scrollregion] 4]

	set width [winfo width $proofwin]
	set height [winfo height $proofwin]

	set left [expr $units*[lindex $hget 2]+[lindex $allbbox 0]]
	set top [expr $units*[lindex $vget 2]+[lindex $allbbox 1]]
	set right [expr $left+$width]
	set bottom [expr $top+$height]

	if {[lindex $bbox 3]+10>$bottom} {
	    $proofwin yview [expr ([lindex $bbox 3]+10-$height-[lindex $allbbox 1])/$units]
	} elseif {[lindex $bbox 1]-10<$top} {
	    $proofwin yview [expr ([lindex $bbox 1]-10-[lindex $allbbox 1])/$units]
	}

	if {[lindex $bbox 2]+10>$right} {
	    $proofwin xview [expr ([lindex $bbox 2]+10-$width-[lindex $allbbox 0])/$units]
	} elseif {[lindex $bbox 0]-10<$left} {
	    $proofwin xview [expr ([lindex $bbox 0]-10-[lindex $allbbox 0])/$units]
	}				      

	set pwid [expr [lindex $bbox 2]-[lindex $bbox 0]]
	set phit [expr [lindex $bbox 3]-[lindex $bbox 1]]

	if {[parse-bool [get-option circleCurrent]]} {
	    $proofwin create oval \
		[expr [lindex $bbox 0]-$pwid/2.8] \
	    [expr [lindex $bbox 1]-$phit/2.8] \
	    [expr [lindex $bbox 2]+$pwid/2.8] \
	    [expr [lindex $bbox 3]+$phit/2.8] \
	    -tags "$path $path.outline current-circle [ancestors $path $top .desc]" \
	    -outline [get-option currentColor] \
	    -width 2
    }
    
    set curpath $path
    }
}

proc clear-message {top} {
    if [winfo exists $top] {
	$top.message config -text ""
    }
}

proc show-message {top text} {
    $top.message config -text $text
    after 5000 "clear-message $top"
}

proc gen-ps {top psfile landscape} {
    global canvcolors

    set w $top.fr.c

    set bbox [$w bbox all]

    $w postscript \
	-file $psfile \
	-x [lindex $bbox 0] \
	-width [expr [lindex $bbox 2]-[lindex $bbox 0]] \
	-y [lindex $bbox 1] \
	-height [expr [lindex $bbox 3]-[lindex $bbox 1]] \
	-pageheight 8.5i \
	-rotate [expr {$landscape ? "yes" : "no"}]
    show-message $top "Saved PS to $psfile"
}


proc setup-dag-win {title icon PSname win_name class} {
    reset-options
    catch {destroy $win_name}
    set top [toplevel $win_name -geometry 400x400 -class $class -bd 2 -relief raised]
    pack propagate $top 0
    wm title $top $title
    wm iconname $top $icon
    wm minsize $top 100 100
    wm maxsize $top 10000 10000
    set fr [frame $top.fr]
    pack $fr -expand yes -fill both
    set sbwidth 12
    frame $fr.bottom -width $sbwidth
    set c [canvas $fr.c -xscroll "$fr.bottom.hscroll set" -yscroll "$fr.vscroll set" \
	      -height 1 -width 1 -bd 3 -relief ridge]
    create-dag $c
    frame $fr.bottom.right -height 18 -width 18 -bd 3 -relief flat
    scrollbar $fr.vscroll -width $sbwidth -bd 3 -relief ridge \
	-command "$c yview"
    scrollbar $fr.bottom.hscroll -width $sbwidth -bd 3 -relief ridge \
	-command "$c xview" -orient horiz
    pack $fr.bottom -side bottom -fill x
    pack $fr.bottom.right -side right
    pack $fr.bottom.hscroll -side bottom -fill x
    pack $fr.vscroll -side right -fill y
    pack $c -expand yes -fill both
    label $top.message -text ""
    pack $top.message -fill x -side bottom
    button $top.dismiss -text "Dismiss" -command "destroy $win_name" -bd 2
    pack $top.dismiss -side left -padx 2 -pady 2
    menubutton $top.ps -text "Gen PS" -menu $top.ps.menu -relief raised -bd 2
    menu $top.ps.menu
    $top.ps.menu add command -label Portrait -command "gen-ps $top $PSname 0"
    $top.ps.menu add command -label Landscape -command "gen-ps $top $PSname 1"
    pack $top.ps -side left -padx 2 -pady 2
    button $top.help -text "Help" -bd 2 \
	-command "help-$class $win_name"
    pack $top.help -side right -padx 2 -pady 2
    menubutton $top.conf -text Config -menu $top.conf.menu -relief raised -bd 2
    pack $top.conf -side right -padx 2 -pady 2
    menu $top.conf.menu
    $top.conf.menu add cascade -label "Horiz. Separation" \
	-command "set conf_menu_orient x" \
	-menu $top.conf.menu.sep
    $top.conf.menu add cascade -label "Vert. Separation" \
	-command "set conf_menu_orient y" \
	-menu $top.conf.menu.sep
    menu $top.conf.menu.sep
    $top.conf.menu.sep add command -label 5 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 5; dagwin-layout $c"
    $top.conf.menu.sep add command -label 10 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 10; dagwin-layout $c"
    $top.conf.menu.sep add command -label 20 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 20; dagwin-layout $c"
    $top.conf.menu.sep add command -label 50 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 50; dagwin-layout $c"
    $top.conf.menu.sep add command -label 100 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 100; dagwin-layout $c"
    $top.conf.menu.sep add command -label 200 \
	-command "option add Tk$top*\${conf_menu_orient}Sep 200; dagwin-layout $c"
    $top.conf.menu.sep add command -label Custom... \
	-command "make-setter $top \$conf_menu_orient"
    return $c
}

proc make-setter {top orient} {
    set win $top.${orient}Sep
    catch {destroy $win}

    toplevel $win -class Setter

    if {$orient=={x}} {
	wm title $win "Horizontal separation"
	wm iconname $win "Horiz sep"
    } else {
	wm title $win "Vertical separation"
	wm iconname $win "Vert sep"
    }

    label $win.lab -text Separation:
    pack $win.lab -side left
    entry $win.ent -width 10 -relief sunken
    bind $win.ent <Return> "option add Tk$top*${orient}Sep \[%W get\]; dagwin-layout $top.fr.c; destroy $win"
    pack $win.ent -side left
    focus $win.ent
}


# Theory hierarchy support

proc module-hierarchy {name file directory dag} {
    catch {frame .th-hier}
    set win \
	[setup-dag-win \
	     "Theory hierarchy for $name in $directory$file" \
	     "Theory Hierarchy" \
	     $directory${name}_hier.ps \
	     [string tolower .th-hier.$name] \
	     TheoryHierarchy]
    .th-hier.$name configure -bg [get-option background]
    dag-bind-move $win {} Control 1 both
    $win bind :theory <Enter> "module-highlight $win"
    $win bind :theory <Leave> "module-unhighlight $win"
    $win bind :theory <1> "select-theory $win"
    foreach item $dag {
	set th [lindex $item 0]
	set succs [lindex $item 1]
	$win create text 0 0 -text $th -tags "$th $th.real :theory" -anchor n
	dag-add-item $win $th $succs {}
    }
    $win lower dagline
    dag-layout $win $name
    canvas-set-scroll $win 1
}
    
proc select-theory {win} {
    upvar #0 dag-$win dag

    set id [$win find withtag current]
    set item $dag(idtotag,$id)

    emacs-eval "(find-theory \"$item\")"
}

proc module-highlight {win} {
    upvar #0 dag-$win dag

    set id [$win find withtag current]
    set item $dag(idtotag,$id)

    $win dtag :hier_highlight
    $win addtag :hier_highlight withtag $item
    $win addtag :hier_highlight withtag dagline.to$item
    $win addtag :hier_highlight withtag dagline.from$item

    my-foreground $win :hier_highlight [get-option highlight]
}

proc module-unhighlight {win} {
    my-foreground $win :hier_highlight [get-option foreground]
}


# Called from wish.lisp to set up a proof

proc setup-proof {name theory directory counter interactive} {
    global curpath
    catch {frame .proof}
    set pw \
	[setup-dag-win \
	     "Proof of $name in $theory" \
	     "PVS Proof" \
	     $directory${theory}_$name.ps \
	     .proof.$theory-$name \
	     Proof]
    .proof.$theory-$name configure -bg [get-option background]

    if {$interactive} {
	if {[info exists curpath]} {
	    unset curpath
	}
	set proofwin $pw
    }

    dag-bind-move $pw .desc Control 1 to
    dag-bind-move $pw {} Control 2 both
    if {$interactive} {
	$pw bind sequent <1> "show-sequent $pw $theory-$name-top"
    }
    $pw bind rule <1> "get-full-rule $pw $theory-$name-top"
    bind $pw <Destroy> "+pvs-send {(stop-displaying-proof $counter)}"
    bind $pw <Destroy> {+
	foreach kid [winfo children .] {
	    if {[string match .sequent* $kid]} {
		destroy $kid
	    }
	}
    }
}    

proc reset-options {} {
    option clear
    option add Tk.foreground black startupFile

    if {[tk colormodel .]=={color}} {
	option add Tk.highlight red startupFile
	option add Tk.currentColor DarkOrchid startupFile
	option add Tk.circleCurrent no startupFile
	option add Tk.tccColor green4 startupFile
	option add Tk.doneColor blue startupFile
	option add Tk.ancestorColor firebrick startupFile
    } else {
	option add Tk.highlight @gray startupFile
	option add Tk.currentColor black startupFile
	option add Tk.circleCurrent yes startupFile
	option add Tk.tccColor black startupFile
	option add Tk.doneColor @gray startupFile
	option add Tk.ancestorColor black startupFile
    }

    option add Tk.abbrevLen 35 startupFile

    option add Tk.maxHeight 30 startupFile

    option add Tk*proof*xSep 10 startupFile
    option add Tk*proof*ySep 20 startupFile
    option add Tk*th-hier*xSep 50 startupFile
    option add Tk*th-hier*ySep 100 startupFile
}

proc get-option {opt {win .}} {
    set upper [string toupper [string range $opt 0 0]][string range $opt 1 end]
    option get $win $opt $upper
}

proc parse-bool {str} {
    set val 0
    catch {
	if "{$str}" {
	    set val 1
	} 
    }

    return $val
}

proc help-Proof {top} {
    set win $top.helptext
    catch {destroy $win}
    toplevel $win -relief raised -bd 2
    message $win.text -aspect 390 -text "This is a proof display.  The turnstiles represent sequents, and are connected by proof commands.

The mouse has the following bindings:

Left on turnstile - display the corresponding sequent
Left on rule      - expand the rule if not already expanded
C-Left on turnstile or rule - moves the subtree rooted at that pair
C-Middle on turnstile or rule - moves the turnstile/rule pair only"
    button $win.dismiss -text Dismiss -command "destroy $win"
    pack $win.text -side top
    pack $win.dismiss -side left -padx 2 -pady 2
}

proc help-TheoryHierarchy {top} {
    set win $top.helptext
    catch {destroy $win}
    toplevel $win -relief raised -bd 2
    message $win.text -aspect 390 -text "This is a theory hierarchy display.  Each name represents a theory, and the arcs represent IMPORTINGs between theories, where the imported theory is below the importing theory.

The mouse has the following bindings:

Left on theory name - display that theory in an Emacs buffer
C-Left on theory name - moves the name"
    button $win.dismiss -text Dismiss -command "destroy $win"
    pack $win.text -side top
    pack $win.dismiss -side left -padx 2 -pady 2
}
