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
* Description:  This class is responsible for providing the enhanced
 *                localisation services.
 *
*/

package com.nokia.tools.themeinstaller.localisation;

import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Observable;
import java.util.Observer;
import java.util.Vector;

import com.nokia.tools.themeinstaller.defrep.DefinitionRepository;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperationEvent;
import com.nokia.tools.themeinstaller.installationmanager.Lock;

/**
 * This class is responsible for providing the enhanced localisation services.
 */
public class Localisation implements ILocalisation
    {

    // The filename for temporary dtd file.
    private static String COMPOSED_DTD_FILE = "composed";

    // The extension for dtd file's filename.
    private static String DTD_FILE_EXTENSION = ".dtd";

    // Localisation settings of the theme
    private Settings iSettings;

    // File operation observer for copy operations
    private Observer iCopyObserver;

    // Lock for waiting the copy operation completion
    private Lock iCopyLock;

    // Stored file operation event
    private FileOperationEvent iCopyEvent;

    // Definition Repository
    private DefinitionRepository iDefRep;

    /**
     * Constructor.
     * @param aSettings Localisation settings of a theme
     */
    public Localisation( Settings aSettings )
        {
        iSettings = aSettings;
        iDefRep = DefinitionRepository.getInstance();
        iCopyLock = new Lock();
        iCopyObserver = new Observer()
            {
            public void update( Observable aFileOperation, Object aEvent )
                {
                // Store the event
                iCopyEvent = ( FileOperationEvent ) aEvent;
                // Open the lock
                iCopyLock.unLock();
                }
            };
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.localisation.ILocalisation#getSettings()
     */
    public Settings getSettings()
        {
        return iSettings;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.localisation.ILocalisation#findDTD()
     */
    public File composeDTD( String aFileName, int aLanguage ) throws IOException
        {
        // Create a temp dtd file
        File composed = File.createTempFile(
                COMPOSED_DTD_FILE, DTD_FILE_EXTENSION );
        composed.deleteOnExit();

        // Copy the main dtd contents to the temp dtd
        copyDTDContents( findDTD( aFileName ), composed, false );

        // Loc settings: include settings
        Enumeration includes = iSettings.getIncludes().elements();
        IncludeSetting incl = null;
        Enumeration inclEntities = null;
        File inclFile = null;

        // Variables for localisation reading/writing
        String entity = null;
        String locString = null;
        String filename = null;
        Hashtable entities = new Hashtable();
        Integer[] formatArgs = { new Integer( aLanguage ) };

        // Process all include element
        while( includes.hasMoreElements() )
            {
            incl = ( IncludeSetting )includes.nextElement();

            filename = String.format( incl.getFile(), formatArgs );

            // Find the DTD to include from
            inclFile = FileSearch.findFile( incl.getSearchTree(), filename, true );

            // Include entities to the composed dtd file
            if( incl.isIncludeAll() )
                {
                // Append the whole dtd to include to the composed one
                copyDTDContents( inclFile, composed, true );
                }
            else
                {
                // Read the entities to include
                inclEntities = incl.getEntities().elements();
                while( inclEntities.hasMoreElements() )
                    {
                    entity = ( String )inclEntities.nextElement();
                    locString = DTDReader.readEntity( inclFile, entity );
                    entities.put( entity, locString );
                    }
                }
            }

        // Create and return a temporary DTD file being composed
        return DTDComposer.writeEntitiesToDtd( composed, entities, true );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.localisation.ILocalisation#findDTD(java.lang.String)
     */
    public File findDTD( String aFileName ) throws IOException
        {
        // Use the file search to find the dtd file
        Vector searchTree = iSettings.getSearchTree();
        return FileSearch.findFile( searchTree, aFileName, true );
        }

    /**
     * Uses Definition Repository to copy DTD file contents to another DTD file.
     * The method is synchronous and waits for the operation completion.
     * @param aSource Source file
     * @param aDestination Destination file
     * @param aAppend Append to the destination file if it already exists
     * @throws IOException if reading/writing from/to a DTD file fails
     */
    private void copyDTDContents( File aSource, File aDestination, boolean aAppend )
        throws IOException
        {
        iDefRep.copy( aSource, aDestination, aAppend, iCopyObserver );
        iCopyLock.lock();

        if( iCopyEvent.getErrorCode() != FileOperationEvent.OPERATION_SUCCESSFUL )
            {
            throw new IOException( "Localisation: DTD contents copy failed: " +
                    iCopyEvent.getErrorCode() +  ", File: " +
                    iCopyEvent.getFile().getPath() );
            }
        }

    }
