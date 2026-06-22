# ext2spice.tcl — reads INPUT_GDS, extracts parasitics, writes SPICE
# Usage: magic -dnull -noconsole -rcfile FinFET14nm.magicrc < ext2spice.tcl
# Environment variables set before invocation:
#   INPUT_GDS  — absolute path to GDS file
#   OUTPUT_DIR — directory to write extracted.spice

set input_gds $env(INPUT_GDS)
set output_dir $env(OUTPUT_DIR)

gds readonly true
gds read $input_gds

# Get top cell (last in the list is the top-level)
set cells [cellname list allcells]
set topcell [lindex $cells end]

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
