#!/bin/sh
echo "Converting $1 to $2"
infile=$1
outfile=$2
QT_X11_NO_MITSHM=1 xvfb-run --auto-servernum --server-args '-screen 0, 1280x1024x24' \
/usr/bin/klayout -z -rd infile=$infile -rd outfile=$outfile -r image_png.rb



