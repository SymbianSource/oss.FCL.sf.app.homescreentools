============================================================================
Read me for ThemeInstaller Tool                                   24.03.2009
============================================================================

Product description:
====================
ThemeInstaller Tool (XML2ODT) converts the theme files into a binary form and installs these binary
files into folders defined in the property file. By default these folders 
are the folders from where emulator/hardware loads the theme.

Main features:
==============
- Single theme install
- Multiple themes install
- Localization support

System requirements:
====================

Minimum:
- Microsoft Windows XP Professional, Service Pack 2, Service Pack 3, or 
  Microsoft Windows XP Home Edition, Service Pack 2, or any edition of
  Microsoft Windows Vista.
- 512 MB of RAM.
- 430 MB of free disk space.
- 1.5-GHz processor.
- Display supporting 16-bit colour at 1,280 x 1,024-pixel resolution.

Recommended:
- Microsoft Windows XP Professional, Service Pack 2, Service Pack 3, or 
  Microsoft Windows XP Home Edition, Service Pack 2, or any edition of
  Microsoft Windows Vista.
- 1 GB of RAM.
- 430 MB of free disk space.
- 2.8-GHz processor.
- Display supporting 24-bit colour at 1,280 x 1,024-pixel resolution.
- Sound card.


How to Run Themeinstaller:
====================================
- There must not be spaces in the directory names of the path where ThemeInstaller 
is placed.
- If you are using the version that has JRE bundled, use 
./jre1.5.0_12/jre-1_5_0_12-windows-i586-p.exe to install runtime environment.
- After having JRE installed, edit the ThemeInstaller.bat file using a text editor
and set the variable of JRE_BIN_DIR to point to the directory where the java executable
is located at. E.g. before editing the line would look like: 
set JRE_BIN_DIR=".\jre1.5.0_12\bin" 
- After editing the same line could look like (depending on where the JRE has been 
installed): set JRE_BIN_DIR="C:\Program files\Java\jre1.5.0_12\bin"

----------------------------------------------------------------------------
Copyright (c) 2009 Nokia Corporation and/or its subsidiary(-ies).
All rights reserved.

This component and the accompanying materials are made available
under the terms of the License "Eclipse Public License v1.0"
which accompanies this distribution, and is available
at the URL "http://www.eclipse.org/legal/epl-v10.html".