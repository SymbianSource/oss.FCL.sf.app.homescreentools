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
* Description:  Contains one include settings for theme localisation.
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.util.Vector;

/**
 * Contains one include settings for theme localisation.
 */
public class IncludeSetting
    {

    // File to include from
    private String iFile;

    // Include all entities
    private boolean iIncludeAll;

    // Search tree
    private Vector iSearchTree;

    // Entities to include
    private Vector iEntities;



    /**
     * Constructor.
     */
    public IncludeSetting()
        {
        iSearchTree = new Vector();
        iEntities = new Vector();
        }

    /**
     * Get the file to include from.
     * @return the file
     */
    public String getFile()
        {
        return iFile;
        }

    /**
     * Get the search tree.
     * @return the search tree
     */
    public Vector getSearchTree()
        {
        return iSearchTree;
        }

    /**
     * Get the entities to include.
     * @return the entities to include
     */
    public Vector getEntities()
        {
        return iEntities;
        }

    /**
     * Is include all entities flag set.
     * @return true if all entities in the file should be included
     */
    public boolean isIncludeAll()
        {
        return iIncludeAll;
        }

    /**
     * Add an entity to include.
     * @param aEntity the entity to include
     */
    public void addEntity( String aEntity )
        {
        iEntities.add( aEntity );
        }

    /**
     * Add a search directory for the file.
     * @param aDir Search directory
     */
    public void addSearchTree( Vector aSearchTree )
        {
        iSearchTree.addAll( aSearchTree );
        }

    /**
     * Set the file to include from.
     * @param aFile the search pattern for the file
     */
    public void setFile( String aFile )
        {
        iFile = aFile;
        }

    /**
     * Set include all entities flag.
     * @param aIncludeAll true if all entities in the file should be included
     */
    public void setIncludeAll( boolean aIncludeAll )
        {
        iIncludeAll = aIncludeAll;
        }

    }
