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
* Description:  This class contains meta information about the theme.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Hashtable;

/**
 * This class contains meta information about the theme.
 */
public class ODTHeader extends Hashtable
    {
    // Default serial version UID
    private static final long serialVersionUID = 1L;

    // Header fields
    public static final String ApplicationUID = "ApplicationUID";
    public static final String ProviderUID = "ProviderUID";
    public static final String ThemeUID = "ThemeUID";
    public static final String ProviderName = "ProviderName";
    public static final String ThemeFullName = "ThemeFullName";
    public static final String ThemeShortName = "ThemeShortName";
    public static final String ThemeVersion = "ThemeVersion";
    public static final String ScreenSizeX = "ScreenSizeX";
    public static final String ScreenSizeY = "ScreenSizeY";
    public static final String Language = "Language";
    public static final String Flags = "Flags";

    /**
     * Gets binary representation of ODTHeader
     * @return binary representation of ODTHeader
     * @throws IOException if stream I/O fails
     * @throws ODTException if header externalization fails
     */
    public byte[] getBinaryODTHeader() throws IOException, ODTException
        {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        ODTDataOutputStream dos = new ODTDataOutputStream( baos );

        byte[] binaryODTHeader = null;

        try
            {
            // Externalize header contents to the byte stream
            if(null!=get(ApplicationUID))
        	dos.writeUnsignedInt32( ( ( Long )get( ApplicationUID ) ).longValue() );
            if(null!=get(ProviderUID))
            dos.writeUnsignedInt32( ( ( Long )get( ProviderUID ) ).longValue() );
            if(null!=get(ThemeUID))
            dos.writeUnsignedInt32( ( ( Long )get( ThemeUID ) ).longValue() );
            if(null!=get(ProviderName))
            dos.writeString16( ( String )get( ProviderName ) );
            if(null!=get(ThemeFullName))
            dos.writeString16( ( String )get( ThemeFullName ) );
            if(null!=get(ThemeShortName))
            dos.writeString16( ( String )get( ThemeShortName ) );
            if(null!=get(ThemeVersion))
           
            dos.writeString16( ( String )get( ThemeVersion ) );
           
            dos.writeInt32( ( ( Integer )get( ScreenSizeX ) ).intValue() );
            dos.writeInt32( ( ( Integer )get( ScreenSizeY ) ).intValue() );
            dos.writeInt32( ( ( Integer )get( Language ) ).intValue() );
            dos.writeInt32( ( ( Integer )get( Flags ) ).intValue() );
            binaryODTHeader = baos.toByteArray();
            }
        catch( Exception e )
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

        return binaryODTHeader;
        }
    }
