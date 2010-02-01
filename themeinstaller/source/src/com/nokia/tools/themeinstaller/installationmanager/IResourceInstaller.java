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
* Description:  Interface for resource installer
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.IOException;
import java.util.Vector;

import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;
import com.nokia.tools.themeinstaller.odtconverter.ODTResource;

/**
 * Interface for resource installer.
 */
public interface IResourceInstaller
    {

    /**
     * Install a list of resource files. Copies resource files and creates
     * a list of ODT Resources.
     * @param aResources List of resource files to install
     * @param aHeader ODT Header for determining the install location. The
     * header is not altered
     * @return List of created ODT Resources
     * @throws IOException if resource file copying fails
     */
    public Vector installResources(
            Vector aResources,
            ODTHeader aHeader ) throws IOException;


    /**
     * Install a resource file. Copies the resource file and creates
     * an ODT Resource.
     * @param aResource The resource file to install
     * @param aHeader ODT Header for determining the install location. The
     * header is not altered
     * @return Created ODT Resource
     * @throws IOException if resource file can not be copied
     */
    public ODTResource installResource( ThemeResource aResource,
                                        ODTHeader aHeader ) throws IOException;

    /**
     * Puts ODT file itself as a resource
     * @param aHeader ODT Header of the ODT to add as resource. The header
     * itself is not altered
     * @param aNameSpace Theme name space
     * @return new ODTResource object
     */
    public ODTResource createODTResource( ODTHeader aHeader,
                                          String aNameSpace );

    }
