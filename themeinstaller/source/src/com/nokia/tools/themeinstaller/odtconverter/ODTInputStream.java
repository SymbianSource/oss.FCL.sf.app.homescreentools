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
* Description:  Implements ODTInputStream
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;

/**
 * Implements ODTInputStream
 */
public class ODTInputStream extends InputStream
    {

    /** ODTDocument */
    ODTDocument iODTDocument;

    /** ByteArrayOutputStream for binary representations */
    ByteArrayOutputStream iBaos;

    /** ODTDataOutputStream for writing data to stream */
    ODTDataOutputStream iODTDos;

    /** byte array for read */
    byte[] iByteArray = null;

    /** index for reading byte array */
    int iIndex = 0;

    /* Literal delimiter is used in separation of theme header and
    other data in ODT-streaming. */
    private static final char DELIM = '#';

    // Symbian CDirectFileStore needs these
    private static final int WRITE_ONCE_FILE_STORE_UID = 268435511;
    private static final int UNKNOWN_MEDIA_UID = 73066445;

   /**
    * Constructor
    * @param aODTDocument
    * @throws ODTException
    */
    public ODTInputStream( ODTDocument aODTDocument ) throws ODTException
        {
        iODTDocument = aODTDocument;
        iBaos = new ByteArrayOutputStream();
        iODTDos = new ODTDataOutputStream( iBaos );
        getBinaryRepresentations();
        }

    /**
     * gets binary representations of ODTHeader, ODTResources and DOMDocument
     * @throws ODTException
     */
    private void getBinaryRepresentations() throws ODTException
        {
        // first write stuff needed by Symbian CDirectFileStore, then
        // get and write ODT material
        try
            {
            // write first uid
            iODTDos.writeInt32( WRITE_ONCE_FILE_STORE_UID );

            // write two 0, for keeping stream valid in native side
            iODTDos.writeInt( 0 );
            iODTDos.writeInt( 0 );

            // write second uid
            iODTDos.writeInt32( UNKNOWN_MEDIA_UID );

            // write index where ODT header starts
            iODTDos.writeInt32( 20 );

            // get and write ODT header
            iBaos.write( iODTDocument.getODTHeader().getBinaryODTHeader() );

            // write delimiter
            iODTDos.writeInt16( DELIM );

            // write resource count
            int resCount = iODTDocument.getODTResources().size();
            iODTDos.writeInt32( resCount );

            // get and write ODTResources
            for ( Enumeration resources = iODTDocument.getODTResources()
                    .elements(); resources.hasMoreElements(); )
                {
                ODTResource odtResource = ( ODTResource ) resources
                        .nextElement();
                iBaos.write( odtResource.getBinaryODTResource() );
                }

            // get and write DOMDocument
            DOMExternalizer domExt =
                          new DOMExternalizer( iODTDocument.getDOMDocument() );
            iBaos.write( domExt.getByteArray() );
            }
        catch( IOException e )
            {
            throw new ODTException( e.getMessage() );
            }
        }

    /* (non-Javadoc)
     * @see java.io.InputStream#close()
     */
    public void close() throws IOException
        {
        iODTDos.close();
        iBaos.close();
        }

    /* (non-Javadoc)
     * @see java.io.InputStream#read()
     */
    public int read() throws IOException
        {
        if( iByteArray == null )
            {
            iByteArray = iBaos.toByteArray();
            }
        if( iIndex >= iByteArray.length )
            {
            iByteArray = null;
            return -1;
            }

        byte b = iByteArray[iIndex++];
        // because 0xff byte is -1, which is used as end of stream value,
        // we must return 0xff int which is 255.
        if( b == (byte)0xff )
            {
            return 0xff;
            }
        return b;
        }
    }
