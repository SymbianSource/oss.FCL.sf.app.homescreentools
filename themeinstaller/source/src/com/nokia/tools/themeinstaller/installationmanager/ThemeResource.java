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
* Description:  Class representing resource data in theme manifest
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

/**
 * Class representing resource data in theme manifest.
 */
public class ThemeResource
    {

    // File name
    private String iFileName;

    // Cache type
    private int iCacheType;

    // Locking policy
    private int iLockingPolicy;

    // Name space
    private String iNameSpace;

    // Resource type
    private int iResourceType;

    // Mime type
    private String iMimeType;

    /**
     * Constructs a new theme resource.
     * @param aFileName Name of the resource file
     * @param aCacheType Resource cache type
     * @param aLockingPolicy Resource locking policy
     * @param aNameSpace Name space
     * @param aResourceType Resource type
     * @param aMimeType Mime type
     */
    public ThemeResource( String aFileName,
                          int aCacheType,
                          int aLockingPolicy,
                          String aNameSpace,
                          int aResourceType,
                          String aMimeType )
        {
        iFileName = aFileName;
        iCacheType = aCacheType;
        iLockingPolicy = aLockingPolicy;
        iNameSpace = aNameSpace;
        iResourceType = aResourceType;
        iMimeType = aMimeType;
        }

    /**
     * Get resource file name.
     * @return the file name
     */
    public String getFileName()
        {
        return iFileName;
        }

    /**
     * Get resource cache type.
     * @return the cache type
     */
    public int getCacheType()
        {
        return iCacheType;
        }

    /**
     * Get locking policy.
     * @return the locking policy
     */
    public int getLockingPolicy()
        {
        return iLockingPolicy;
        }

    /**
     * Get name space.
     * @return the name space
     */
    public String getNameSpace()
        {
        return iNameSpace;
        }

    /**
     * Get resource type.
     * @return the resource type
     */
    public int getResourceType()
        {
        return iResourceType;
        }

    /**
     * Get resource mime type.
     * @return the resource mime type
     */
    public String getMimeType()
        {
        return iMimeType;
        }

    /**
     * Set resource type.
     * @param aResourceType new resource type
     */
    public void setResourceType( int aResourceType )
        {
        iResourceType = aResourceType;
        }

    /**
     * Set mime type.
     * @param aResourceType new mime type
     */
    public void setMimeType( String aMimeType )
        {
        iMimeType = aMimeType;
        }

    }
