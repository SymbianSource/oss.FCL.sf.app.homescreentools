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
* Description:  File operation for storing an ODT file to the file system
 *
*/


package com.nokia.tools.themeinstaller.defrep.operations;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * Operation for storing data to the file system.
 */
public class StoreOperation extends FileOperation
    {

    // CONSTANTS
    private static final int READ_BUFFER_SIZE = 1024;

    // Input stream for data input
    private InputStream iStream;

    /**
     * Create a store operation
     *
     * @param aDestination Destination file
     * @param aStream Input stream containing the data
     */
    public StoreOperation( File aDestination, InputStream aStream )
        {
        iFile = aDestination;
        iStream = aStream;
        }

    public void run()
        {
        int error = FileOperationEvent.UNKNOWN_ERROR;

        try
            {
            doStoreOperation();
            error = FileOperationEvent.OPERATION_SUCCESSFUL;
            }
        catch ( IOException ioe )
            {
            error = FileOperationEvent.IO_ERROR;
            }

        super.finished( iFile, error );
        }

    private void doStoreOperation()
        throws IOException
        {
        // Overwrite the existing file, if any
        if( iFile.exists() )
            {
            iFile.delete();
            }

        // Create the required directory structure for the destination file
        // (ignore return value)
        FileOperationUtils.createDirs( iFile );

        FileOutputStream output = null;

        try
            {
            output = new FileOutputStream( iFile );

            // Create a buffer for the data transfer
            byte[] buffer = new byte[ READ_BUFFER_SIZE ];
            int i = 0;

            // Read data to the buffer and write it to the output stream until
            // the whole stream is processed
            while( ( i = iStream.read( buffer ) ) != -1 )
                {
                output.write( buffer, 0, i );
                }
            }
        finally
            {
            if( output != null )
                {
                output.close();
                }
            }
        }

    }
