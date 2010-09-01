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
* Description:  Interface to the Definition Repository
 *
*/


package com.nokia.tools.themeinstaller.defrep;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Observer;

import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;


/**
 * Interface to the Defition Repository.
 */
public interface IDefinitionRepository
    {
    /**
     * Copy a file.
     * @param aSource Source file
     * @param aDestination Destination file
     * @param aAppend Append to the destination file if it exists
     * @param aListener File operation listener to inform operation completion
     */
    public void copy( File aSource,
                      File aDestination,
                      boolean aAppend,
                      Observer aListener );

    /**
     * Store a file to the file system.
     *
     * @param aDestination Destination file
     * @param aStream Source stream
     * @param aListener File operation listener to inform operation completion
     */
    public void store( File aDestination,
                       InputStream aStream,
                       Observer aListener );

    /**
     * Store an ODT Document to the file system.
     *
     * @param aDestination Destination root folder for the ODT file. Normally,
     * the epocroot is specified.
     * @param aHeader ODT header
     * @param aStream Input stream containing the ODT file contents
     * @param aListener File operation listener
     * @throws IOException if required properties can not be read from the
     * property file.
     */
    public void storeODT( File aDestination,
                          ODTHeader aHeader,
                          InputStream aStream,
                          Observer aListener ) throws IOException;

    /**
     * Copies resource to destination folder
     *
     * @param aSource Source file
     * @param aDestination Root of destination folder
     * @param aHeader ODT header
     * @throws IOException if required properties can not be read, or
     * some other IO exception during copy operation
     */
    public void copyResource( File aSource,
                              File aDestination,
                              ODTHeader aHeader,
                              Observer aListener ) throws IOException;

    /**
     * Create a path and file name of an ODT file.
     *
     * @param aDestination Root destination
     * @param aHeader ODT header
     * @return Path to the ODT file
     */
    public String createODTPath( File aDestination, ODTHeader aHeader );

    }

