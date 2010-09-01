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
* Description:  This class contains data about theme resource.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Hashtable;

/**
 * This class contains data about theme resource.
 */
public class ODTResource extends Hashtable
    {
    // Default serial version UID
    private static final long serialVersionUID = 1L;

    // ODT Resource properties, externalized
    public static final String LockingPolicy = "LockingPolicy";
    public static final String CacheType = "CacheType";
    public static final String ResourceType = "ResourceType";
    public static final String ResourceID = "ResourceID";
    public static final String NameSpace = "NameSpace";
    public static final String FileName = "FileName";
    public static final String MimeType = "MimeType";

    // Size and offset are hard-coded because they are not used in Xuikon
    private static final int SIZE = 0;
    private static final int OFFSET = 0;

    // Name of the temporary file, not externalized
    public static final String TempFileName = "TempFileName";


    /**
     * Gets binary representation of one ODTResource
     * @return binary representation of one ODTResource
     * @throws IOException
     * @throws ODTException
     */
    public byte[] getBinaryODTResource() throws IOException, ODTException
        {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        ODTDataOutputStream dos = new ODTDataOutputStream( baos );

        byte[] binaryODTResource = null;

        try
            {
            // Write properties of the resource to the byte stream
            dos.writeInt32( ( ( Integer ) get( LockingPolicy ) ).intValue() );
            dos.writeInt32( ( ( Integer ) get( CacheType ) ).intValue() );
            dos.writeInt32( ( ( Integer ) get( ResourceType ) ).intValue() );
            dos.writeString16( ( String ) get( ResourceID ) );
            dos.writeString16( ( String ) get( NameSpace ) );
            dos.writeString16( ( String ) get( FileName ) );
            dos.writeString8( ( String ) get( MimeType ) );
            dos.writeInt32( SIZE );
            dos.writeInt32( OFFSET );

            binaryODTResource = baos.toByteArray();
            }
        catch ( Exception e )
            {
            throw new ODTException( e.getMessage() );
            }
        finally
            {
            // Close the streams
            if( dos != null )
                {
                dos.close();
                }
            if( baos != null )
                {
                baos.close();
                }
            }

        return binaryODTResource;
        }
    }
