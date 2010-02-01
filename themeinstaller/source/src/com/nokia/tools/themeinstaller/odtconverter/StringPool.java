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
* Description:  String pool for DOM Externalizer.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Vector;

/**
 * String pool is a set of strings where a string is only listed once.
 */
public class StringPool
    {

    // The pool for storing the strings
    private Vector iStringPool;

    /**
     * Constructor.
     */
    public StringPool()
        {
        iStringPool = new Vector();
        }

    /**
     * Add a string to the pool. Each string is added only once.
     * @param aString String to add
     * @return Index in the pool
     */
    public int addString( String aString )
        {
        if( aString == null )
            {
            aString = "";
            }
        if( !iStringPool.contains( aString ) )
            {
            iStringPool.addElement( aString );
            }
        return iStringPool.lastIndexOf( aString );
        }

    /**
     * Get a string from the pool.
     * @param aIndex Index number of the string
     * @return The requested string
     */
    public String getString( int aIndex )
        {
        return ( String ) iStringPool.elementAt( aIndex );
        }


    /**
     * Get string pool contents in a byte array.
     * @return String pool contents in a byte array
     * @throws IOException if writing to a stream fails
     * @throws ODTException if writing to a stream fails
     */
    public byte[] toByteArray() throws IOException, ODTException
        {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        ODTDataOutputStream dos = new ODTDataOutputStream( baos );
        int count = iStringPool.size();
        byte[] result = null;

        try
            {
            // Write string count and each string to the stream
            dos.writeInt16( count );
            for( int i = 0; i < count; i++ )
                {
                String string = ( String ) iStringPool.elementAt( i );
                dos.writeInt16( string.length() );
                dos.writeString8( string );
                }

            result = baos.toByteArray();
            }
        finally
            {
            if( dos != null )
                {
                dos.close();
                }
            if( baos != null )
                {
                baos.close();
                }
            }

        return result;
        }

    }
