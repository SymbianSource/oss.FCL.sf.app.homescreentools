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
* Description:  Utils for file operations
 *
*/


package com.nokia.tools.themeinstaller.defrep.operations;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;


/**
 * Utils for file operations.
 */
public class FileOperationUtils
    {

    // CONSTANTS
    private static final int READ_BUFFER_SIZE = 1024;
    private static final String REGEXP_PREFIX = "\\";
    private static final char EPOC_DRIVE_SEP = ':';
    private static final String EPOC_PATH_SEP = "\\";
    private static final char EPOC_DRIVE_LETTER_FIRST_U = 'A';
    private static final char EPOC_DRIVE_LETTER_LAST_U = 'Z';
    private static final char EPOC_DRIVE_LETTER_FIRST_L = 'a';
    private static final char EPOC_DRIVE_LETTER_LAST_L = 'z';
    private static final String EPOC32_DIR = "epoc32";

    /**
     * Copy a file to an another location.
     *
     * @param aSource Source file
     * @param aDestination Destination file
     * @param aAppend If true, the source file contents will be appended to the end of
     * the destination file. Otherwise, the original file will be overwritten.
     * @throws FileNotFoundException Thrown if the file can not be found
     * @throws IOException Thrown if IOException occurs, open streams are also closed
     */
    public static void copyFile( File aSource, File aDestination, boolean aAppend )
        throws FileNotFoundException, IOException
        {
        // Overwrite the existing file, if any
        if( aDestination.exists() && !aAppend )
            {
            aDestination.delete();
            }

        // Create the required directory structure for the destination file
        // (ignore return value)
        createDirs( aDestination );

        // Open streams for input and output
        FileInputStream input = new FileInputStream( aSource );
        FileOutputStream output = new FileOutputStream( aDestination, aAppend );

        // Create buffer for the data transfer
        byte[] buffer = new byte[ READ_BUFFER_SIZE ];
        int i = 0;

        try
            {
            // Read data to the buffer and write it to the output stream until
            // the whole file is processed
            while( ( i = input.read( buffer ) ) != -1 )
                {
                output.write( buffer, 0, i );
                }
            }
        finally
            {
            if( input != null )
                {
                input.close();
                }
            if( output != null )
                {
                output.close();
                }
            }
        }

    /**
     * Create the whole directory structure for the file
     *
     * @param aFile File object to be placed at the end of the tree
     * @return true, if new directories were created
     */
    public static boolean createDirs( File aFile )
        {
        // Extract the parent directory
        String parent = aFile.getParent();

        // Create the whole directory structure
        File dir = new File( parent );
        return dir.mkdirs();
        }

    /**
     * Parse Symbian OS file system format path of a Winscw environment path.
     * This method will search for a directory of which name is one character
     * long and from a to z.
     * @param aFile The file to process
     * @return Path and file name in Symbian OS file system. Returns null if
     * the file name can not be parsed.
     */
    public static String parseSymbianFSPath( File aFile )
        {
        String result = null;
        String path = aFile.getPath();

        File file = aFile.getParentFile();

        // Go through all parent directories of the file
        while( file != null )
            {
            // Find a directory of which name is 1 character long
            String name = file.getName();
            if( name.length() == 1 )
                {
                // Check that the directory name is an character
                // from A to Z or a to z
                char c = name.charAt( 0 );
                if( ( c >= EPOC_DRIVE_LETTER_FIRST_U &&
                      c <= EPOC_DRIVE_LETTER_LAST_U  ) ||
                    ( c >= EPOC_DRIVE_LETTER_FIRST_L &&
                      c <= EPOC_DRIVE_LETTER_LAST_L  ) )
                    {
                    result = name;
                    }
                }
            // Stop if already reached to the epoc32 directory
            else if( EPOC32_DIR.equalsIgnoreCase( name ) )
                {
                break;
                }

            file = file.getParentFile();
            }

        if( result != null )
            {
            String pattern = File.separatorChar + result + File.separatorChar;

            // Find the start of the actual path
            int pathStart = path.indexOf( pattern ) + pattern.length();

            // Combine the Symbian OS format path of the drive letter,
            // path separator and rest of the path
            result = result +
                     EPOC_DRIVE_SEP +
                     EPOC_PATH_SEP +
                     path.substring( pathStart );

            // Replace path separators with Epoc ones
            pattern = REGEXP_PREFIX + File.separator;
            String replacement = REGEXP_PREFIX + EPOC_PATH_SEP;
            result = result.replaceAll( pattern, replacement );
            }

        return result;
        }

    /**
     * Parse Symbian OS file system format path of a Winscw environment path.
     * @param aFile The file name to process
     * @return Path and file name in Symbian OS file system. Returns null if
     * the file name can not be parsed.
     */
    public static String parseSymbianFSPath( String aFile )
        {
        File f = new File( aFile );
        return parseSymbianFSPath( f );
        }
    }
