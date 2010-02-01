/*
* Copyright (c) 2007 Nokia Corporation and/or its subsidiary(-ies). 
* All rights reserved.
* This component and the accompanying materials are made available
* under the terms of "Eclipse Public License v1.0"
* which accompanies this distribution, and is available
* at the URL "http://www.eclipse.org/legal/epl-v10.html".
*
* Initial Contributors:
* Nokia Corporation - initial contribution.
*
* Contributors:
*
* Description:  An event for informing about file operation completion
 *
*/


package com.nokia.tools.themeinstaller.defrep.operations;

import java.io.File;

public class FileOperationEvent
    {

    // CONSTANTS
    public static final int OPERATION_SUCCESSFUL = 0;
    public static final int FILE_NOT_FOUND_ERROR = -1;
    public static final int IO_ERROR = -2;
    public static final int UNKNOWN_ERROR = -3;

    // The file related to the operation
    private File iFile;

    // Destination file of the operation (in Symbian OS filesystem)
    private String iDestPath;

    // Error code of the finished operation
    private int iErrorCode;

    /**
     * File operation event constructor.
     *
     * @param aFileName File related to the event
     * @param aErrorCode Error code of the completed operation
     */
    public FileOperationEvent( File aFile, int aErrorCode )
        {
        iFile = aFile;
        iErrorCode = aErrorCode;
        iDestPath = FileOperationUtils.parseSymbianFSPath( iFile );
        }

    /**
     * Get the file.
     * @return The file
     */
    public File getFile()
        {
        return iFile;
        }

    /**
     * Get the error code.
     * @return The error code
     */
    public int getErrorCode()
        {
        return iErrorCode;
        }

    /**
     * Get the destination path in Symbian OS file system.
     * @return the iDestPath Destination path
     */
    public String getDestPath()
        {
        return iDestPath;
        }
    
    /**
     * Get the full destination path in PC file system.
     * @return the iFile's path
     */
    public String getFullDestPath()
        {
        return iFile.getPath();
        }
    }
