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
* Description:  Class for installing theme resources
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Observable;
import java.util.Observer;
import java.util.Vector;

import com.nokia.tools.themeinstaller.defrep.IDefinitionRepository;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperationEvent;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperationUtils;
import com.nokia.tools.themeinstaller.mediaconverter.MediaConverter;
import com.nokia.tools.themeinstaller.odtconverter.MimeTypeResolver;
import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;
import com.nokia.tools.themeinstaller.odtconverter.ODTResource;
import com.nokia.tools.themeinstaller.odtconverter.ThemeStatusResolver;

/**
 * Class for installing theme resources.
 */
public class ResourceInstaller implements IResourceInstaller
    {

    // CONSTANTS
    private static final String MBM_SUFFIX = "mbm";
    private static final char FILE_EXT_SEPARATOR = '.';

    // Definition repository for accessing the file storage services
    private IDefinitionRepository iDefRep;

    // File operation event for observing file operations
    private FileOperationEvent iEvent;

    // Destination root directory
    private File iDestinationDir;

    // Data directory
    private String iDataDir;

    // Media converter for converting resources
    private MediaConverter iMediaConverter;

    // Mime type resolver for resolving resource type
    private MimeTypeResolver iMimeResolver;

    // Observer for monitoring file operation completions
    private Observer iFileCopyObserver;

    // For storing temporary files.
    private Vector iTempFiles;

    // Lock for asynchronous operations.
    private Lock iLock;

    /**
     * Constructor.
     * @param aDefRep Definition Repository for accessing the file storage
     * @param aDestinationDir Destination root directory
     * @param aDataDir Data directory containing the theme sources
     * @param aNameSpace Theme name space
     * @throws IOException if Media Converter can not be created
     */
    public ResourceInstaller( IDefinitionRepository aDefRep,
                              File aDestinationDir,
                              String aDataDir ) throws IOException
        {
        iDefRep = aDefRep;
        iDestinationDir = aDestinationDir;
        iDataDir = aDataDir;
        iMediaConverter = new MediaConverter();
        iMimeResolver = new MimeTypeResolver();
        iTempFiles = new Vector();
        iLock = new Lock();

        // Create an observer for monitoring file copy operation completions
        iFileCopyObserver = new Observer()
            {
            public void update( Observable aFileOperation, Object aEvent )
                {
                // Store the event
                iEvent = ( FileOperationEvent ) aEvent;
                // Open the lock
                iLock.unLock();
                }
            };
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.odtconverter.installationmanager.IResourceInstaller#installResources(java.util.Vector, com.nokia.tools.odtconverter.ODTHeader)
     */
    public Vector installResources(
            Vector aResources,
            ODTHeader aHeader ) throws IOException
        {
        Vector result = new Vector();
        Enumeration resources = aResources.elements();

        // Process all resource files
        while ( resources.hasMoreElements() )
            {
            result.add( installResource( ( ThemeResource ) resources.nextElement(), aHeader ) );
            }

        return result;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.odtconverter.installationmanager.IResourceInstaller#installResource(com.nokia.tools.odtconverter.installationmanager.ThemeResource, com.nokia.tools.odtconverter.ODTHeader)
     */
    public ODTResource installResource( ThemeResource aResource,
                                        ODTHeader aHeader ) throws IOException
        {
        // Create the ODT resource
        ODTResource res = createResource( iDataDir, aResource );

        // Copy file to correct location
        File f = new File(
                iDataDir + ( String )res.get( ODTResource.TempFileName ) );
        iDefRep.copyResource(
                f,
                iDestinationDir,
                aHeader,
                iFileCopyObserver );
        // Wait for file copying
        iLock.lock();

        if ( iEvent.getErrorCode() == FileOperationEvent.OPERATION_SUCCESSFUL )
            {
            deleteTemporaryFile( iEvent.getFile().getName() );
            }
        else
            {
            throw new IOException( "Resource file copying failed: "
                    + f.getPath() );
            }

        // Set the actual resource location (in Symbian file system) to resource
        res.put( ODTResource.FileName, iEvent.getDestPath() );
        return res;
        }

    /**
     * Delete temporary file.
     *
     * @param aFileName The file name
     *
     * @throws IOException Signals that an I/O exception has occurred.
     */
    private void deleteTemporaryFile( String aFileName ) throws IOException
        {
        Enumeration fileObjects = iTempFiles.elements();

        while ( fileObjects.hasMoreElements() )
            {
            File temp = ( File ) fileObjects.nextElement();
            if ( temp.getName().equals( aFileName ) )
                {
                if ( !temp.delete() )
                    {
                    throw new IOException( "Temporary file deletion failed: "
                            + aFileName );
                    }
                else
                    {
                    iTempFiles.remove( temp );
                    deleteTemporaryFile( aFileName );
                    }
                }
            }
        }


    /* (non-Javadoc)
     * @see com.nokia.tools.odtconverter.installationmanager.IResourceInstaller#createODTResource(com.nokia.tools.odtconverter.ODTHeader)
     */
    public ODTResource createODTResource( ODTHeader aHeader, String aNameSpace )
        {
        ODTResource res = new ODTResource();
        String odtPath = null;

        // Create ODT file path
        odtPath = iDefRep.createODTPath( iDestinationDir, aHeader );

        // Convert the path to Symbian OS file system format
        odtPath = FileOperationUtils.parseSymbianFSPath( odtPath );

        res.put( ODTResource.FileName, odtPath );
        res.put( ODTResource.CacheType,
                new Integer( ManifestFactory.CACHE_TYPE_CACHE_FILE ) );

        // If EXnThemeStatusLicenceeDefault flag is set,
        // locking policy is E_XN_LOCKED
        int flags = ( ( Integer )aHeader.get( ODTHeader.Flags ) ).intValue();
        if ( ( flags & ThemeStatusResolver.E_XN_THEME_STATUS_LICENCEE_DEFAULT ) != 0 )
            {
            res.put( ODTResource.LockingPolicy,
                    new Integer( ManifestFactory.E_XN_LOCKED ) );
            }
        else
            {
            res.put( ODTResource.LockingPolicy,
                    new Integer( ManifestFactory.E_XN_UNLOCKED ) );
            }

        // ODT file's mime type is "unknown"
        res.put( ODTResource.MimeType, MimeTypeResolver.UNKNOWN_MIME_TYPE );
        res.put( ODTResource.NameSpace, aNameSpace );
        res.put( ODTResource.ResourceID, aHeader
                        .get( ODTHeader.ThemeShortName ) );
        res.put( ODTResource.ResourceType, new Integer(
                MimeTypeResolver.E_RESOURCEODT ) );
        return res;
        }


    /**
     * Creates ODT resource from given node
     * @param aItem DOM Node to be added
     * @param aDataDirectory Resource directory
     * @return new ODTResource object
     * @throws IOException if media file can not be converter
     */
    private ODTResource createResource( String aDataDirectory,
                                        ThemeResource aItem ) throws IOException
        {
        ODTResource res = new ODTResource();

        String tempFileName = null;
        String filename = aItem.getFileName();
        int cacheType = aItem.getCacheType();

        // Determine the need for media conversion
        if( cacheType == ManifestFactory.CACHE_TYPE_CACHE_FILE ||
            cacheType == ManifestFactory.CACHE_TYPE_CACHE_MEMORY )
            {
            // Convert the media file
            tempFileName = convertMedia( aDataDirectory + filename );
            }
        else
            {
            // No media conversion
            tempFileName = filename;
            }

        // Remove directories and separators from the file name
        int fileNameIndex = tempFileName.lastIndexOf( File.separatorChar );
        if( fileNameIndex > -1 )
            {
            tempFileName = tempFileName.substring( fileNameIndex + 1 );
            }

        // Update resource type after media conversion
        aItem.setResourceType( iMimeResolver.getResourceType( tempFileName ) );
        aItem.setMimeType( iMimeResolver.getMimeType( tempFileName ) );

        // Set temporary file name that is not externalized. It is required
        // only for copying the resource file in a case that media conversion
        // has changed the file name and extension.
        res.put( ODTResource.TempFileName, tempFileName );

        // Set properties that are externalized. The file name is set after the
        // resource file is copied to the correct location.
        res.put( ODTResource.CacheType, new Integer(cacheType ));
        res.put( ODTResource.ResourceID, filename );
        res.put( ODTResource.LockingPolicy, new Integer(aItem.getLockingPolicy() ));
        res.put( ODTResource.NameSpace, aItem.getNameSpace() );
        res.put( ODTResource.MimeType, aItem.getMimeType() );
        res.put( ODTResource.ResourceType, new Integer(aItem.getResourceType() ));
        return res;
        }

    /**
     * Uses MediaConverter to converts media to MBM
     * @param aFilename File to convert
     * @return Filename of converted resource
     * @throws IOException File conversion fails
     */
    private String convertMedia( String aFilename ) throws IOException
        {
        ArrayList files = new ArrayList();
        files.add( aFilename );
        int dotPosition = aFilename.lastIndexOf( FILE_EXT_SEPARATOR ) + 1;
        String destinationImage =
            aFilename.substring( 0, dotPosition ) + MBM_SUFFIX;

        if ( dotPosition == 0 )
            {
            destinationImage = aFilename + FILE_EXT_SEPARATOR + MBM_SUFFIX;
            }

        String filePrefix = destinationImage.substring( 0,
                destinationImage.lastIndexOf( FILE_EXT_SEPARATOR ) );
        File destFile = new File( destinationImage );
        int index = 1;

        // create unique name to not overwrite any existing files
        while( destFile.exists() )
            {
            destinationImage =
                filePrefix + index++ + FILE_EXT_SEPARATOR + MBM_SUFFIX;
            destFile = new File( destinationImage );
            }

        iMediaConverter.convertMedia( files, destinationImage );
        iTempFiles.add( destFile );
        return destinationImage;
        }

    }
