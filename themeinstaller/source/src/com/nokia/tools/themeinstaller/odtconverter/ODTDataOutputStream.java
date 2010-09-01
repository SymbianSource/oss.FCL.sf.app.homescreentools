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
* Description:  Implements ODTDataOutputStream
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;

import com.ibm.icu.text.UnicodeCompressor;

/**
 * Implements ODTDataOutputStream. Helper class for writing strings
 * and numeric values to stream so that native implementation reads
 * them properly.
 *
 */
public class ODTDataOutputStream extends DataOutputStream
    {

    public ODTDataOutputStream( OutputStream aStream )
        {
        super( aStream );
        }

    /**
     * Write unsigned 32-bit integer.
     * Using long as Java's Integer value is restricted to
     * range -2^31 ... 2^31-1
     * @param aValue the value as long
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    public void writeUnsignedInt32( long aValue ) throws IOException, ODTException
        {
        // Using range of unsigned integer
        // Values bigger than 2^32-1 are not allowed
        if ( aValue < 0 || aValue > 0xFFFFFFFFL )
            {
            throw new ODTException(
                    "ODTDataOutputStream writeUnsignedInt32s failed, value out of range" );
            }

        byte[] bArray = new byte[ 4 ];
        bArray[ 3 ] = ( byte ) ( ( aValue & 0xFF000000L ) >> 24 );
        bArray[ 2 ] = ( byte ) ( ( aValue & 0x00FF0000L ) >> 16 );
        bArray[ 1 ] = ( byte ) ( ( aValue & 0x0000FF00L ) >> 8 );
        bArray[ 0 ] = ( byte ) ( aValue & 0x000000FFL );

        int len = bArray.length;
        super.write( bArray, 0, len );
        }

    /**
     * Writes int to stream for native Int32
     * @param aValue
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    public void writeInt32( int aValue ) throws ODTException, IOException
        {
        byte[] bArray = new byte[4]; // we want 32 bit integer
        ByteBuffer buf = ByteBuffer.wrap( bArray );
        // byte order in native is LITTLE_ENDIAN
        buf.order( ByteOrder.LITTLE_ENDIAN );
        buf.putInt( aValue );

        if( buf.hasArray() )
            {
            bArray = buf.array();
            }
        else
            {
            throw new ODTException( "ODTDataOutputStream writeInt32 failed" );
            }

        int len = bArray.length;
        super.write( bArray, 0, len );
        }

    /**
     * Writes int to stream for native Int16
     * @param aValue
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    public void writeInt16( int aValue ) throws ODTException, IOException
        {
        Integer value = new Integer( aValue );
        byte[] bArray = new byte[2]; // we want 16 bit integer
        ByteBuffer buf = ByteBuffer.wrap( bArray );
        // byte order in native is LITTLE_ENDIAN
        buf.order( ByteOrder.LITTLE_ENDIAN );
        buf.putShort( value.shortValue() );

        if( buf.hasArray() )
            {
            bArray = buf.array();
            }
        else
            {
            throw new ODTException( "ODTDataOutputStream writeInt16 failed" );
            }

        int len = bArray.length;
        super.write( bArray, 0, len );
        }

    /**
     * Writes double to stream for native TReal64
     * @param aValue
     * @throws ODTException
     * @throws IOException
     */
    public void writeTReal64( double aValue ) throws ODTException, IOException
        {
        byte[] bArray = new byte[8]; // we want 64 bit TReal
        ByteBuffer buf = ByteBuffer.wrap( bArray );
        buf.order( ByteOrder.LITTLE_ENDIAN );
        buf.putDouble( aValue );

        if( buf.hasArray() )
            {
            bArray = buf.array();
            }
        else
            {
            throw new ODTException( "ODTDataOutputStream writeTReal64 failed" );
            }

        int len = bArray.length;
        super.write( bArray, 0, len );
        }

    /**
     * Writes string to stream for native HBufC8
     *
     * See Symbian common sources for more information:
     *
     * src\common\generic\syslibs\store\USTRM\US_FUNC.CPP
     * ExternalizeL(const TDesC8& aDes8,RWriteStream& aStream)
     *
     * src\common\generic\syslibs\store\INC\U32STD.INL
     * TDesHeader::TDesHeader(const TDesC8& aDes8)
     *
     * @param aS String to write
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    public void writeString8( String aS ) throws ODTException, IOException
        {
        byte[] ba = aS.getBytes();
        int len = ba.length;

        writeCardinality( len, true );

        super.write( ba, 0, len );
        }

    /**
     * Writes string to stream for native HBufC16.
     *
     * See Symbian common sources for more information:
     *
     * src\common\generic\syslibs\store\USTRM\US_FUNC.CPP
     * ExternalizeL(const TDesC16& aDes16,RWriteStream& aStream)
     *
     * src\common\generic\syslibs\store\INC\U32STD.INL
     * TDesHeader::TDesHeader(const TDesC16& aDes16)
     *
     * @param aS String to write
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    public void writeString16( String aS ) throws ODTException, IOException
        {
        // Take length of the String for calculating the cardinality
        // The cardinality is calculated of the original length of the string
        // (before compress) because the original length is again valid when
        // the string is uncompressed in the Symbian side.
        int clen = aS.length();

        // Using UnicodeCopressor to compress string. The Unicode Compression
        // is also used in Unicode builds of Symbian.
        byte[] ba = UnicodeCompressor.compress( aS );
        int len = ba.length;

        writeCardinality( clen, false );

        super.write( ba, 0, len );
        }

    /**
     * Calculates HBufC8 and HBufC16 string length for native stream.
     *
     * See Symbian common sources for more information:
     *
     * src\common\generic\syslibs\store\USTRM\US_UTL.CPP
     * TCardinality::ExternalizeL(RWriteStream& aStream)
     *
     * src\common\generic\syslibs\store\INC\U32STD.INL
     * TDesHeader::TDesHeader(const TDesC16& aDes16)
     * TDesHeader::TDesHeader(const TDesC8& aDes8)
     *
     * @param aLenght string length
     * @param a8bit set true for 8-bit descriptors, this adds one to the count
     * @throws IOException if writing to a stream fails
     * @throws ODTException if data conversion fails
     */
    private void writeCardinality( int aLenght, boolean a8bit ) throws IOException, ODTException
        {
        int count = aLenght * 2;

        if( a8bit )
            {
            count = count + 1;
            }

        if( count <= ( Byte.MAX_VALUE ) )
            {
            super.writeByte( count << 1 );
            }
        else if( count <= ( 65535 >>> 2 ) )
            {
            writeInt16( ( count << 2 ) + 1 );
            }
        else
            {
            writeInt32( ( count << 3 ) + 3 );
            }
        }

    }
