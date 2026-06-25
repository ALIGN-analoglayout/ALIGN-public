# ext2spice.tcl — reads INPUT_GDS, extracts parasitics, writes SPICE
# Usage: magic -dnull -noconsole -rcfile FinFET14nm.magicrc < ext2spice.tcl
# Environment variables set before invocation:
#   INPUT_GDS  — absolute path to GDS file
#   OUTPUT_DIR — directory to write extracted.spice

set input_gds $env(INPUT_GDS)
set output_dir $env(OUTPUT_DIR)

gds readonly true
gds read $input_gds

# Find the top-level cell: ALIGN writes it first in the GDS and names it
# {CIRCUIT_UPPER}_0. Match by prefix so layout variants are handled.
set cells [cellname list allcells]
set circuit_upper [string toupper $env(CIRCUIT)]
set topcell ""
foreach cell $cells {
    if {[string match "${circuit_upper}_*" $cell]} {
        set topcell $cell
        break
    }
}
# Fallback: first cell in list (ALIGN top-level is written first)
if {$topcell eq ""} {
    set topcell [lindex $cells 0]
}
puts "ext2spice: loading top cell '$topcell'"

load $topcell
select top cell

# Run extraction
extract all

# Write extracted SPICE
ext2spice rthresh 0
ext2spice cthresh 0
ext2spice format ngspice
ext2spice -o ${output_dir}/extracted.spice

# Clean up .ext files
foreach f [glob -nocomplain *.ext] { file delete $f }

quit
