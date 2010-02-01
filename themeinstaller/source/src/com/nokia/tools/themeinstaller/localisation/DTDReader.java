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
* Description:  Read entities from dtd files
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.nokia.tools.themeinstaller.logger.LogWriter;
import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;

/**
 * Reads entities from dtd files.
 */
public class DTDReader
    {

    /** The Regular expression for entity. */
    private static final String ENTITY_REGEX = "<!ENTITY(\\s*)%s(.*)>";

    /** The Regular expression for entity's value. */
    private static final String VALUE_REGEX = "(\")(.*)(\")";

    /** Line separator */
    private static final String LINE_SEPARATOR =
            System.getProperty( "line.separator" );

    /** Property key for character encoding of DTD files */
    private static final String ENCODING_KEY = "dtd_encoding";

    /**
     * Read DTD Entities. Reads a set of DTD files and searches
     * for localised string defined in a entity named aLocString.
     * If there are more than one instances found, the one that
     * is found first is returned.
     *
     * @param aDtdFiles DTD files containing entities
     * @param aLocString Entity's localisation string
     *
     * @return Localised string
     *
     * @throws IOException Signals that an I/O exception has occurred.
     */
    public static String readFiles( Vector aDtdFiles, String aLocString )
            throws IOException
        {
        String tempResult = null;
        Vector results = new Vector();
        for ( int i = 0; i < aDtdFiles.size(); i++ )
            {
            tempResult = readEntity( ( File ) aDtdFiles.get( i ), aLocString );

            if ( tempResult != null )
                {
                results.add( tempResult );
                }
            }
        if ( results.isEmpty() )
            {
            return null;
            }
        else
            {
            return ( String ) results.firstElement();
            }

        }

    /**
     * Read localized entity from the dtd.
     *
     * @param aDTD DTD file containing the localization
     * @param aLocString Localization string
     * @return Localized entity
     * @throws IOException if FileInputStream can not be opened
     */
    public static String readEntity( File aDTD, String aLocString )
            throws IOException
        {
        StringBuffer strbuf = new StringBuffer();

        // Read the assumed character encoding of DTD files
        String encoding =
                ConverterProperties.getInstance().getProperty( ENCODING_KEY );

        BufferedReader rdr = null;
        if( encoding != null )
            {
            // Use specified encoding
            rdr = new BufferedReader( new InputStreamReader(
                    new FileInputStream( aDTD ), encoding ) );
            }
        else
            {
            // Use default encoding
            LogWriter.getInstance().logWarning( "DTDReader: Character " +
            		"encoding of DTD files is not specified in the " +
            		"properties file, using system default encoding." );

            rdr = new BufferedReader( new InputStreamReader(
                    new FileInputStream( aDTD ) ) );
            }

        // Add all lines from the DTD file to the buffer
        for ( String line = rdr.readLine(); line != null; line = rdr.readLine() )
            {
            strbuf.append( line + LINE_SEPARATOR );
            }

        String[] formatArguments = { aLocString };
        String regex = String.format( ENTITY_REGEX, formatArguments );

        // Search for an entity containing the aLocString
        String result = findString( regex, strbuf.toString() );

        if ( result != null )
            {
            // Search for the entity's value
            result = findString( VALUE_REGEX, result );

            // Remove "-marks from the value
            result = result.replaceAll( "\"", "" );
            }

        return result;
        }

    /**
     * Find a substring. Also verifies that exactly one match is found.
     *
     * @param aRegex Regular expression for matching
     * @param aSearchString String for searching
     * @return Found string
     */
    private static String findString( String aRegex, String aSearchString )
        {
        String result = null;
        Pattern pattern = Pattern.compile( aRegex );
        Matcher matcher = pattern.matcher( aSearchString );
        int count = 0;
        while ( matcher.find() )
            {
            result = matcher.group();
            count++;
            }

        if ( count > 1 )
            {
            throw new IllegalArgumentException( "DTD parsing: "
                    + "found more than one localized value for the "
                    + "entity" );
            }

        return result;
        }

    }
