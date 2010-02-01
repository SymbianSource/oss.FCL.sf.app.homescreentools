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
* Description:  Contains the localisation settings that were defined in the
 *                localisation settings file.
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.util.Vector;

/**
 * Contains the localisation settings that were defined in the localisation
 * settings file. One instance contains settings for one theme.
 */
public class Settings
    {

    // Theme application uid
    private long iAppUid;

    // Theme provider uid
    private long iProviderUid;

    // Theme uid
    private long iThemeUid;

    // Main DTD file search tree
    private Vector iSearchTree;

    // Include settings
    private Vector iIncludeSettings;

    /**
     * Constructor.
     */
    public Settings()
        {
        iSearchTree = new Vector();
        iIncludeSettings = new Vector();
        }

    /**
     * Get application uid.
     * @return the application uid
     */
    public long getAppUid()
        {
        return iAppUid;
        }

    /**
     * Get provider uid.
     * @return the provider uid
     */
    public long getProviderUid()
        {
        return iProviderUid;
        }

    /**
     * Get theme uid.
     * @return the theme uid
     */
    public long getThemeUid()
        {
        return iThemeUid;
        }

    /**
     * Get the search tree of the main DTD file.
     * @return Search tree
     */
    public Vector getSearchTree()
        {
        return iSearchTree;
        }

    /**
     * Get all include settings of a theme.
     * @return List of include settings
     */
    public Vector getIncludes()
        {
        return iIncludeSettings;
        }

    /**
     * Set application uid.
     * @param aAppUid the application uid to set
     */
    public void setAppUid( long aAppUid )
        {
        iAppUid = aAppUid;
        }

    /**
     * Set provider uid.
     * @param aProviderUid the provider uid to set
     */
    public void setProviderUid( long aProviderUid )
        {
        iProviderUid = aProviderUid;
        }

    /**
     * Set theme uid.
     * @param aThemeUid the theme uid to set
     */
    public void setThemeUid( long aThemeUid )
        {
        iThemeUid = aThemeUid;
        }

    /**
     * Add main DTD search tree.
     * @param aSearchTree Search tree
     */
    public void addSearchTree( Vector aSearchTree )
        {
        iSearchTree.addAll( aSearchTree );
        }

    /**
     * Add include settings of the theme.
     * @param aInclude Include settings
     */
    public void addInclude( IncludeSetting aInclude )
        {
        iIncludeSettings.add( aInclude );
        }
    }
