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
* Description:  Searches files from given directories
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.io.File;
import java.io.FileFilter;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Searches files that's name matches the regular expression.
 * Search operations can be executed in one or multiple directories
 * and also including subfolders in the search can activated.
 *
 * There are two versions for searching: recursive and non-recursive.
 * Recursive version is used when flooding the search to subfolders
 */
public class FileSearch
    {
    private static Vector iFiles;


    /**
     * Find files in directories.
     *
     * @param aRootDirs The root directories where the search is initiated
     * @param aFileNameExpression The file name expression
     * @param aIncludeSubfolders Include subfolders in the search or not
     * @param aAllowSameName Allow same filenames
     *
     * @return Found files in a vector
     */
    public static Vector findFiles( Vector aRootDirs,
            String aFileNameExpression, boolean aIncludeSubfolders,
            boolean aAllowSame )
        {
        Vector allFiles = new Vector();
        Vector fileFromOneSearch = new Vector();

        for ( int i = 0; i < aRootDirs.size(); i++ )
            {
            fileFromOneSearch = findFiles( ( String ) aRootDirs.elementAt( i ),
                    aFileNameExpression, aIncludeSubfolders, aAllowSame );

            for ( int j = 0; j < fileFromOneSearch.size(); j++ )
                {
                if ( aAllowSame && !allFiles.contains( fileFromOneSearch.get( j ) ) )
                    {
                    allFiles.add( fileFromOneSearch.get( j ) );
                    }
                if ( !aAllowSame
                        && !hasSameName( allFiles, ( File ) fileFromOneSearch.get( j ) ) )
                    {
                    allFiles.add( fileFromOneSearch.get( j ) );

                    }
                }
            }

        return allFiles;
        }

    /**
     * Find files in directories.
     *
     * @param aRootDirs The root directories where the search is initiated
     * @param aFileNameExpression The file name expression
     * @param aIncludeSubfolders Include subfolders in the search or not
     *
     * @return Found files in a vector
     */
    public static Vector findFiles( Vector aRootDirs,
            String aFileNameExpression, boolean aIncludeSubfolders )
        {
        return findFiles( aRootDirs, aFileNameExpression, aIncludeSubfolders,
                true );
        }

    /**
     * Find one file in directories. Returns the first one found.
     *
     * @param aRootDirs The root directories where the search is initiated
     * @param aFileNameExpression The file name expression
     * @param aIncludeSubfolders Include sub folders in the search or not
     *
     * @return Found file
     */
    public static File findFile( Vector aRootDirs,
            String aFileNameExpression, boolean aIncludeSubfolders )
        {
        Vector results = findFiles( aRootDirs, aFileNameExpression, aIncludeSubfolders,
                true );

        if( results.size() == 0 )
            {
            throw new IllegalArgumentException( "Localisation: File Search: " +
            		"File not found: " + aFileNameExpression );
            }

        return ( File ) results.elementAt( 0 );
        }

    /**
     * Find files in directory.
     *
     * @param aRootDir The root directory where the search is initiated
     * @param aFileNameExpression The file name expression
     * @param aIncludeSubfolders Include subfolders in the search or not
     * @param aAllowSameName Allow same filenames
     *
     * @return Found files in a vector
     */
    public static Vector findFiles( String aRootDir,
            String aFileNameExpression, boolean aIncludeSubfolders,
            boolean aAllowSameName )
        {

        iFiles = new Vector();
        // If subfolders included, use recursive version
        if ( aIncludeSubfolders )
            {
            findFilesInSubfolder( new File( aRootDir ), aFileNameExpression,
                    aAllowSameName );
            }
        // If no subfolders included, use non-recursive version
        if ( !aIncludeSubfolders )
            {
            findFilesInFolder( new File( aRootDir ), aFileNameExpression,
                    aAllowSameName );
            }

        return iFiles;

        }

    /**
     * Find files in directory.
     *
     * @param aRootDir The root directory where the search is initiated
     * @param aFileNameExpression The file name expression
     * @param aIncludeSubfolders Include subfolders in the search or not
     *
     * @return Found files in a vector
     */
    public static Vector findFiles( String aRootDir,
            String aFileNameExpression, boolean aIncludeSubfolders )
        {
        return findFiles( aRootDir, aFileNameExpression, aIncludeSubfolders, true );
        }

    /**
     * Find files in folder. Non-recursive version
     *
     * @param dir Directory to search in
     * @param aFileNameExpression The file name expression
     * @param aAllowSameName Allow same filename
     */
    private static void findFilesInFolder( File dir,
            final String aFileNameExpression, boolean aAllowSameName )
        {
        // Condition that file must fulfill
        FileFilter fileFilter = new FileFilter()
            {
            public boolean accept( File file )
                {
                return ( !file.isDirectory() && match( aFileNameExpression,
                        file.getName() ) );
                }
            };

        // Files that match the condition
        File[] files = dir.listFiles( fileFilter );

        for ( int i = 0; i < files.length; i++ )
            {
            if ( aAllowSameName )
                {
                iFiles.add( files[ i ] );
                }
            if ( !aAllowSameName && !hasSameName( iFiles, files[ i ] ) )
                {
                iFiles.add( files[ i ] );
                }
            }

        }

    /**
     * Find files in folder and it's subfolder. Recursive version
     *
     * @param dir Root directory to start search
     * @param aFileNameExpression the a file name expression
     * @param aAllowSameName Allow same filenames
     */
    private static void findFilesInSubfolder( File dir,
            final String aFileNameExpression, boolean aAllowSameName )
        {

        // Flood the search to subdirectories:
        if ( dir.isDirectory() )
            {

            File[] files = dir.listFiles();

            for ( int i = 0; i < files.length; i++ )
                {
                findFilesInSubfolder( files[ i ], aFileNameExpression,
                        aAllowSameName );
                }
            }
        // If not directory, add files that match conditions
        else
            {
            if ( match( aFileNameExpression, dir.getName() ) )
                {
                if ( aAllowSameName )
                    {
                    iFiles.add( dir );
                    }
                if ( !aAllowSameName && !hasSameName( iFiles, dir ) )
                    {
                    iFiles.add( dir );
                    }

                }
            }
        }

    /**
     * Match regular expression with string.
     *
     * @param patternStr Regular expression for match
     * @param input String to compare the regular expression
     *
     * @return true, if input matches the regular expression
     */
    private static boolean match( String patternStr, CharSequence input )
        {
        Pattern pattern = Pattern.compile( patternStr );
        Matcher matcher = pattern.matcher( input );
        if ( matcher.matches() )
            {
            return true;
            }
        return false;
        }

    /**
     * Checks if vector already has file with same name.
     *
     * @param aFiles Files to check
     * @param aFile Reference file
     *
     * @return true, if vector already has file with same name
     */
    private static boolean hasSameName( Vector aFiles, File aFile )
        {
        for ( int i = 0; i < aFiles.size(); i++ )
            {
            if ( ( ( File ) aFiles.get( i ) ).getName()
                    .equals( aFile.getName() ) )
                {
                return true;
                }
            }
        return false;
        }

    }
