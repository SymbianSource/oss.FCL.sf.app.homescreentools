@rem
@rem Copyright (c) 2009 Nokia Corporation and/or its subsidiary(-ies).
@rem All rights reserved.
@rem This component and the accompanying materials are made available
@rem under the terms of "Eclipse Public License v1.0"
@rem which accompanies this distribution, and is available
@rem at the URL "http://www.eclipse.org/legal/epl-v10.html".
@rem
@rem Initial Contributors:
@rem Nokia Corporation - initial contribution.
@rem
@rem Contributors:
@rem
@rem Description: 
@rem

@ECHO OFF

REM Configuration
setlocal
set JRE_BIN_DIR=%JAVA_6_HOME%\bin

REM Verify that the JAVA_6_HOME exists
if not exist %JAVA_6_HOME%\bin\java.exe goto lookforsymseej6
set JRE_BIN_DIR="%JAVA_6_HOME%\bin"
goto jpathexists


:lookforsymseej6
REM Verify that symsee java6 exists
if not exist "C:\APPS\j2sdk_1.6.0_02\jre\bin\java.exe" goto lookforjava_home
set JRE_BIN_DIR="C:\APPS\j2sdk_1.6.0_02\jre\bin"
goto jpathexists


:lookforjava_home
REM Verify that the JAVA_HOME exists
if not exist %JAVA_HOME%\bin\java.exe goto assigndefaultjrepath
set JRE_BIN_DIR="%JAVA_HOME%\bin"
goto jpathexists


:assigndefaultjrepath
set JRE_BIN_DIR=%JAVA_HOME%\bin"

:jpathexists
set INSTALL_DIR="."

REM Verify that the JRE executable exists
if not exist %JRE_BIN_DIR%\java.exe goto jreexecutablenotfound

REM Verify that the theme installer exists
if not exist %INSTALL_DIR%\ThemeInstaller.jar goto installernotfound

REM Execute ThemeInstaller
%JRE_BIN_DIR%\java -Dfile.encoding=ISO8859_1 -classpath %INSTALL_DIR%/ThemeInstaller.jar;%INSTALL_DIR%/lib//batik/batik-util.jar;%INSTALL_DIR%/lib/xml-apis-ext/xml-apis-ext.jar;%INSTALL_DIR%/lib/batik/batik-css.jar;%INSTALL_DIR%/lib/xerces/xercesImpl.jar;%INSTALL_DIR%/lib/icu/icu4j_3_2.jar com.nokia.tools.themeinstaller.ui.ThemeInstaller %1 %2 %3 %4 %5 %6
goto exitpoint

:jreexecutablenotfound
echo.
echo ERROR: Java Runtime Environment not found at %JRE_BIN_DIR%
echo Configure the JRE location in ThemeInstallerMain.bat file and ThemeInstaller.bat.
goto exitpoint

:installernotfound
echo.
echo ERROR: ThemeInstaller.jar not found at %INSTALL_DIR%
echo Configure the install location in ThemeInstallerMain.bat file and ThemeInstaller.bat.
goto exitpoint

:exitpoint