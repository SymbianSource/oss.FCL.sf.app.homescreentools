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
* Description:  Gets the mime- and resource type using file's name extension
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.util.Hashtable;

/**
 * Resolves the MimeType and Resource type of the resource to match the file
 * name used in the Symbian side. This class is following the behavior of the
 * Symbian class XnInstallationHandler.cpp in ...Xuikon\UIManager\src\
 *
 * In Symbian, MimeType is TDataType that has TBuf8 and TUid. The constructor
 * taking a descriptor of TDataType is as follows:
 *
 * If descriptor begins with "x-epoc/x-app", identifying data as a native
 * Symbian type, then the associated UID is set to the UID value which is
 * expected to follow the characters "x-epoc/x-app". If no sensible UID can be
 * extracted from the characters following: "x-epoc/x-app", then the associated
 * UID is set to KNullUid.
 *
 * Else Uid is set to KNullDesc and the descriptor is the descriptor given in
 * parameter.
 *
 * In ...Xuikon\UIManager\src\XnInstallationHandler.cpp
 * (ImportCompatibleResourcesL) MimeType is constructed using the Descriptor
 * that is parsed using file's name extension. Descriptors beginning with
 * "x-epoc/x-app" aren't used so TUid part is not implemented. Some of the types
 * are left empty in XnInstallationHandler.cpp. This represented as
 * EMPTY_MIME_TYPE
 *
 * Resource types are defined in Symbian side class XnResource.h
 *
 */
public class MimeTypeResolver
    {
    private static Hashtable iResourceTypeAndMimeType;

    public static final int E_RESOURCE_NONE = 0;
    public static final int E_RESOURCERLB = 1;
    public static final int E_RESOURCEODT = 2;
    public static final int E_RESOURCEDTD = 3;
    public static final int E_RESOURCEXML = 4;
    public static final int E_RESOURCECSS = 5;
    public static final int E_RESOURCEDAT = 6;
    public static final int E_RESOURCERES = 7;
    public static final int E_RESOURCEFBS = 8;
    public static final int E_RESOURCEMBM = 9;
    public static final int E_RESOURCEMIF = 10;
    public static final int E_RESOURCEBMP = 11;
    public static final int E_RESOURCEJPG = 12;
    public static final int E_RESOURCEJPEG = 13;
    public static final int E_RESOURCEPNG = 14;
    public static final int E_RESOURCEGIF = 15;
    public static final int E_RESOURCEAAC = 16;
    public static final int E_RESOURCEWAV = 17;
    public static final int E_RESOURCEMID = 18;
    public static final int E_RESOURCEMP3 = 19;
    public static final int E_RESOURCEM3G = 20;
    public static final int E_RESOURCESVG = 21;
    public static final int E_RESOURCESWF = 22;
    public static final int E_RESOURCEMIME = 23;
    public static final int E_RESOURCETXT = 24;

    public static final String KRLB_FILE_EXTENSION =  ".r";
    public static final String KODT_FILE_EXTENSION =  ".o";
    public static final String KDTD_FILE_EXTENSION =  ".dtd";
    public static final String KXML_FILE_EXTENSION =  ".xml";
    public static final String KCSS_FILE_EXTENSION =  ".css";
    public static final String KDAT_FILE_EXTENSION =  ".dat";
    public static final String KFBS_FILE_EXTENSION =  ".fbs";
    public static final String KMBM_FILE_EXTENSION =  ".mbm";
    public static final String KMIF_FILE_EXTENSION =  ".mif";
    public static final String KBMP_FILE_EXTENSION =  ".bmp";
    public static final String KJPG_FILE_EXTENSION =  ".jpg";
    public static final String KJPEG_FILE_EXTENSION =  ".jpeg";
    public static final String KPNG_FILE_EXTENSION =  ".png";
    public static final String KGIF_FILE_EXTENSION =  ".gif";
    public static final String KAAC_FILE_EXTENSION =  ".aac";
    public static final String KWAV_FILE_EXTENSION =  ".wav";
    public static final String KMID_FILE_EXTENSION =  ".mid";
    public static final String KMP3_FILE_EXTENSION =  ".mp3";
    public static final String KM3G_FILE_EXTENSION =  ".m3g";
    public static final String KSVG_FILE_EXTENSION =  ".svg";
    public static final String KSWF_FILE_EXTENSION =  ".swf";
    public static final String KTXT_FILE_EXTENSION =  ".txt";

    public static final String KAPAAPPTYPEDES = "x-epoc/x-app";

    public static final String TXT_MIME_TYPE = "text/xml";
    public static final String MBM_MIME_TYPE = "image/x-epoc-mbm";
    public static final String EMPTY_MIME_TYPE = "";
    public static final String EMPTY_FILE_EXTENSION = "";
    public static final String WAV_MIME_TYPE = "audio/x-wav";
    public static final String MIDI_MIME_TYPE = "audio/midi";
    public static final String UNKNOWN_MIME_TYPE = "unknown";

    public static final String NAME_EXTENSION_SEPARATOR = ".";

    /**
     * Instantiates a new mimetype resolver.
     */
    public MimeTypeResolver()
        {
        iResourceTypeAndMimeType = new Hashtable();
        iResourceTypeAndMimeType.put( KRLB_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCERLB ) );
        iResourceTypeAndMimeType.put( KODT_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEODT ) );
        iResourceTypeAndMimeType.put( KDTD_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEDTD ) );
        iResourceTypeAndMimeType.put( KXML_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEXML ) );
        iResourceTypeAndMimeType.put( KCSS_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCECSS ) );
        iResourceTypeAndMimeType.put( KDAT_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEDAT ) );
        iResourceTypeAndMimeType.put( KFBS_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEFBS ) );
        iResourceTypeAndMimeType.put( KMBM_FILE_EXTENSION, new ResourceTypeAndMimeType( MBM_MIME_TYPE, E_RESOURCEMBM ) );
        iResourceTypeAndMimeType.put( KMIF_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEMIF ) );
        iResourceTypeAndMimeType.put( KBMP_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEBMP ) );
        iResourceTypeAndMimeType.put( KJPG_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEJPG ) );
        iResourceTypeAndMimeType.put( KJPEG_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEJPEG ) );
        iResourceTypeAndMimeType.put( KPNG_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEPNG ) );
        iResourceTypeAndMimeType.put( KGIF_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEGIF ) );
        iResourceTypeAndMimeType.put( KAAC_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCEAAC ) );
        iResourceTypeAndMimeType.put( KWAV_FILE_EXTENSION, new ResourceTypeAndMimeType( WAV_MIME_TYPE, E_RESOURCEWAV ) );
        iResourceTypeAndMimeType.put( KMID_FILE_EXTENSION, new ResourceTypeAndMimeType( MIDI_MIME_TYPE, E_RESOURCEMID ) );
        iResourceTypeAndMimeType.put( KMP3_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEMP3 ) );
        iResourceTypeAndMimeType.put( KM3G_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCEM3G ) );
        iResourceTypeAndMimeType.put( KSVG_FILE_EXTENSION, new ResourceTypeAndMimeType( UNKNOWN_MIME_TYPE, E_RESOURCESVG ) );
        iResourceTypeAndMimeType.put( KSWF_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCESWF ) );
        iResourceTypeAndMimeType.put( KTXT_FILE_EXTENSION, new ResourceTypeAndMimeType( EMPTY_MIME_TYPE, E_RESOURCETXT ) );
        }

    /**
     * Gets the MimeType.
     *
     * @param aFileName The file name
     *
     * @return The MimeType
     */
    public String getMimeType( String aFileName )
        {
        return getMimeTypeValue( getFileExtension( aFileName ) );
        }

    /**
     * Gets the resource type.
     *
     * @param aFileName The file name
     *
     * @return The Resource type
     */
    public int getResourceType( String aFileName )
        {
        return getResourceTypeValue( getFileExtension( aFileName ) );
        }

    /**
     * Gets the mimetype value.
     *
     * @param aKey The hashtable key is filen name extension
     *
     * @return The mimetype value
     */
    private String getMimeTypeValue( String aKey )
        {
        if ( iResourceTypeAndMimeType.containsKey( aKey ) )
            {
            ResourceTypeAndMimeType rtamt = ( ResourceTypeAndMimeType ) iResourceTypeAndMimeType.get( aKey );
            return rtamt.getMimeType();
            }
        return EMPTY_MIME_TYPE;
        }

    /**
     * Gets the resource type value.
     *
     * @param aKey The hashtable key is file name extension
     *
     * @return The resource type value
     */
    private int getResourceTypeValue( String aKey )
        {
        if ( iResourceTypeAndMimeType.containsKey( aKey ) )
            {
            ResourceTypeAndMimeType rtamt = ( ResourceTypeAndMimeType ) iResourceTypeAndMimeType.get( aKey );
            return rtamt.getResourceType();
            }
        return E_RESOURCE_NONE;
        }

    /**
     * Gets the file extension.
     *
     * @param aFileName The file name
     *
     * @return The file extension
     */
    private String getFileExtension( String aFileName )
        {
        String fileExtension = "";
        if ( aFileName.contains( NAME_EXTENSION_SEPARATOR ) )
            {
            fileExtension = aFileName.substring(
                    aFileName.lastIndexOf( NAME_EXTENSION_SEPARATOR ),
                    aFileName.length() ).toLowerCase();
            return fileExtension;
            }
        return EMPTY_FILE_EXTENSION;
        }

    /**
     * Inner class for containing mimetype - resource type pairs.
     */
    private static class ResourceTypeAndMimeType
        {
        private String iMimeType;
        private int iResourceType;

        /**
         * Instantiates a new resource type and mime type pair.
         *
         * @param aMimeType The mime type
         * @param aResourceType The resource type
         */
        public ResourceTypeAndMimeType( String aMimeType, int aResourceType )
            {
            iMimeType = aMimeType;
            iResourceType = aResourceType;
            }

        /**
         * Gets the mimetype.
         *
         * @return The mimetype
         */
        public String getMimeType()
            {
            return iMimeType;
            }

        /**
         * Gets the resource type.
         *
         * @return The resource type
         */
        public int getResourceType()
            {
            return iResourceType;
            }

        }

    }
