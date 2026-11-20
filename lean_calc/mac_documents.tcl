# Installed before Tk_Init so Finder events received during startup are retained.
namespace eval ::tk::mac {}
set ::calcDocumentBatches {}
set ::calcDocumentsReady 0
set ::calcDocumentsBusy 0
set ::calcDocumentsScheduled 0
proc ::tk::mac::OpenDocument {args} {
    if {![llength $args]} {return}
    lappend ::calcDocumentBatches $args
    calcScheduleDocuments
}
proc calcScheduleDocuments {} {
    if {$::calcDocumentsReady && !$::calcDocumentsBusy && !$::calcDocumentsScheduled && [llength $::calcDocumentBatches]} {
        set ::calcDocumentsScheduled 1
        after idle calcDrainDocuments
    }
}
proc calcDocumentsReady {} {
    set ::calcDocumentsReady 1
    calcScheduleDocuments
}
proc calcDrainDocuments {} {
    set ::calcDocumentsScheduled 0
    if {!$::calcDocumentsReady || $::calcDocumentsBusy} {return}
    set ::calcDocumentsBusy 1
    try {
        while {[llength $::calcDocumentBatches]} {
            set batch [lindex $::calcDocumentBatches 0]
            set ::calcDocumentBatches [lrange $::calcDocumentBatches 1 end]
            # List expansion preserves spaces, Unicode and Tcl metacharacters.
            calc opendocuments {*}$batch
        }
    } finally {
        set ::calcDocumentsBusy 0
        calcScheduleDocuments
    }
}
