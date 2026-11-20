# All data enters these procedures as Tcl arguments, never evaluated as script.
proc calcObjectsStart {sheet} {
    catch {destroy .objects}
    foreach name [image names] {if {[string match calcObjectPhoto* $name]} {image delete $name}}
    toplevel .objects
    wm title .objects "Sheet objects — $sheet"
    ttk::notebook .objects.tabs
    pack .objects.tabs -fill both -expand 1 -padx 12 -pady 12
    wm geometry .objects 700x440
}
proc calcObjectPage {index title} {
    set frame .objects.tabs.p$index
    ttk::frame $frame
    .objects.tabs add $frame -text $title
    return $frame
}
proc calcCheckPNG {bytes} {
    if {[string length $bytes] < 24 || [string length $bytes] > 1400000 || [string range $bytes 0 7] ne "\x89PNG\r\n\x1a\n"} {error "Choose a PNG image smaller than 1.4 MB."}
    binary scan [string range $bytes 16 23] II width height
    if {$width < 1 || $height < 1 || $width > 4096 || $height > 4096 || $width*$height > 4000000} {error "PNG dimensions must be at most 4096 per side and 4 million pixels."}
}
proc calcReadPNG {path} {
    set file [open $path rb]
    try {set bytes [read $file 1400001]} finally {close $file}
    calcCheckPNG $bytes
    # Decode once to reject malformed PNGs before storing them.
    set picture [image create photo -data $bytes -format png]
    image delete $picture
    return [binary encode base64 -maxlen 0 $bytes]
}
proc calcObjectImage {frame data} {
    set bytes [binary decode base64 -strict $data]
    calcCheckPNG $bytes
    set original [image create photo -data $bytes -format png]
    set scale [expr {max(1,int(ceil([image width $original]/640.0)),int(ceil([image height $original]/340.0)))}]
    set photo [image create photo calcObjectPhoto[string map {. _} $frame]]
    $photo copy $original -subsample $scale $scale
    image delete $original
    ttk::label $frame.image -image $photo
    pack $frame.image -expand 1 -padx 12 -pady 12
}
