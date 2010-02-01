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

REM Execute JAVAVersionChecker
%JRE_BIN_DIR%\java.exe -classpath %INSTALL_DIR% JAVAVersionChecker %1 %2 %3 %4 %5 %6 
goto exitpoint

:jreexecutablenotfound
echo.
echo ERROR: Java Runtime Environment Executable not found at %JRE_BIN_DIR%
echo Configure the JRE location in ThemeInstallerMain.bat file and ThemeInstaller.bat.
goto exitpoint

:exitpoint