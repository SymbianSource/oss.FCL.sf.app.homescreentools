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
* Description:  File operation for copying the installable files
 *
*/


package com.nokia.tools.themeinstaller.defrep.operations;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

/**
 * Operation for copying files.
 */
public class CopyOperation extends FileOperation
    {

    // Destination file
    private File iDestination;

    // Append flag
    private boolean iAppend;

    /**
     * Create a copy operation
     *
     * @param aSource Source file name
     * @param aDestination Destination file name
     * @param aAppend Append to the destination file if it exists
     */
    public CopyOperation( File aSource, File aDestination, boolean aAppend )
        {
        iFile = aSource;
        iDestination = aDestination;
        iAppend = aAppend;
        }

    /* (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    public void run()
        {
        int error = FileOperationEvent.UNKNOWN_ERROR;

        // Perform the copy operation
        try
            {
            FileOperationUtils.copyFile( iFile, iDestination, iAppend );
            error = FileOperationEvent.OPERATION_SUCCESSFUL;
            }
        catch( FileNotFoundException fnfe )
            {
            error = FileOperationEvent.FILE_NOT_FOUND_ERROR;
            }
        catch( IOException ioe )
            {
            error = FileOperationEvent.IO_ERROR;
            }

        // Report results to the operation listeners
        super.finished( iDestination, error );
        }

    }
