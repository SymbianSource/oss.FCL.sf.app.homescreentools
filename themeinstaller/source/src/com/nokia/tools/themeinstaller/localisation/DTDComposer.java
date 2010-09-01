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
* Description:  Composes one dtd file from dtd entities
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;

import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;

/**
 * Composes one dtd file from multiple entities.
 */
public class DTDComposer
    {

    /** The Regular expression for entity. */
    private static final String FORMAT = "<!ENTITY %s \"%s\">";

    /** Line separator */
    private static final String CARRIAGE_RETURN =
            System.getProperty( "line.separator" );

    /** Property key for character encoding of DTD files */
    private static final String ENCODING_KEY = "dtd_encoding";


    /**
     * Returns dtd entity in right format for file writing.
     *
     * @param aEntity the entity
     * @param aLocString the localisable entity value
     *
     * @return Formatted entity
     */
    public static String formatEntity( String aEntity, String aLocString )
        {
        String[] formatArguments = { aEntity, aLocString };
        return String.format( FORMAT, formatArguments );
        }

    /**
     * Write entities to dtd file.
     *
     * @param aDestination Destination file
     * @param aEntities Entity - value pairs in hashtable
     * @param aAppend Append to the original file if it exists
     *
     * @return The dtd file
     *
     * @throws IOException Signals that an I/O exception has occurred.
     */
    public static File writeEntitiesToDtd( File aDestination,
                                           Hashtable aEntities,
                                           boolean aAppend )
        throws IOException
        {

        // Read the assumed character encoding of DTD files
        String encoding =
                ConverterProperties.getInstance().getProperty( ENCODING_KEY );

        BufferedWriter out = null;
        if( encoding != null )
            {
            // Use specified encoding
            out = new BufferedWriter( new OutputStreamWriter(
                    new FileOutputStream( aDestination, aAppend ), encoding ) );
            }
        else
            {
            // Use default encoding
            out = new BufferedWriter( new OutputStreamWriter(
                    new FileOutputStream( aDestination, aAppend ) ) );
            }

        try
            {
            Set entries = aEntities.keySet();
            Iterator it = entries.iterator();

            while ( it.hasNext() )
                {
                String entity = ( String ) it.next();
                String locString = ( String ) aEntities.get( entity );

                out.write( formatEntity( entity, locString ) + CARRIAGE_RETURN );
                }
            }
        finally
            {
            if ( out != null )
                {
                out.close();
                }
            }

        return aDestination;
        }

    }
