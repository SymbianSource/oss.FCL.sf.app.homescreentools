#!/bin/sh

#
# Configuration
#

# Directory where JRE has java executable has been installed to
JRE_BIN_DIR=/home/TransCrescent/rossi/jre1.5.0_12/bin
# Directory where ThemeInstaller has been installed to
TI_DIR=.

#Launch ThemeInstaller

PATH=$JRE_BIN_DIR/:$PATH
java -Dfile.encoding=ISO8859_1 -classpath $TI_DIR/ThemeInstaller.jar:$TI_DIR/lib/batik-util.jar:$TI_DIR/lib/xml-apis-ext.jar:$TI_DIR/lib/batik-css.jar:$TI_DIR/lib/xercesImpl.jar com.nokia.tools.themeinstaller.ui.ThemeInstaller $1 $2 $3 $4 $5 $6
