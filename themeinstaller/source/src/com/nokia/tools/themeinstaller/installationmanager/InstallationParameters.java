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
* Description:  Installation parameters for starting the Installation Manager
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;

/**
 * Installation parameters for starting the Installation Manager.
 */
public class InstallationParameters
    {

    // Manifest file
    private File iManifest;

    // Destination directory
    private File iDestinationDir;

    // Localisation settings
    private File iLocSettings;

    // External properties file
    private File iPropFile;

    /**
     * Constructor.
     * @param aManifest Manifest file
     * @param aDestinationDir Destination directory
     */
    public InstallationParameters( File aManifest, File aDestinationDir )
        {
        iManifest = aManifest;
        iDestinationDir = aDestinationDir;

        // Verify that theme manifest exists
        if( !aManifest.exists() )
            {
            throw new IllegalArgumentException(
                    "Manifest file not found: " + aManifest.getPath() );
            }

        // Verify that destination directory is not an existing file
        if( aDestinationDir.isFile() )
            {
            throw new IllegalArgumentException( "Invalid destination directory: " +
            		aDestinationDir.getPath() );
            }
        }

    /**
     * Get the manifest file.
     * @return the manifest file
     */
    public File getManifest()
        {
        return iManifest;
        }

    /**
     * Get the destination directory.
     * @return the destination directory
     */
    public File getDestinationDir()
        {
        return iDestinationDir;
        }

    /**
     * Get the localisation settings file.
     * @return the localisation settings file
     */
    public File getLocSettings()
        {
        return iLocSettings;
        }

    /**
     * Get the properties file.
     * @return the properties file
     */
    public File getPropFile()
        {
        return iPropFile;
        }

    /**
     * Set the localisation settings file.
     * @param aLocSettings the localisation settings file to set
     */
    public void setLocSettings( File aLocSettings )
        {
        iLocSettings = aLocSettings;

        // Verify that localisation settings are found
        if( aLocSettings != null &&
          ( !aLocSettings.exists() || !aLocSettings.isFile() ) )
            {
            throw new IllegalArgumentException(
                    "Localisation settings file not found: " +
                    aLocSettings.getPath() );
            }
        }

    /**
     * Set the properties file.
     * @param aPropFile the properties file to set
     */
    public void setPropFile( File aPropFile )
        {
        iPropFile = aPropFile;

        // Verify that properties file is found
        if( aPropFile != null &&
          ( !aPropFile.exists() || !aPropFile.isFile() ) )
            {
            throw new IllegalArgumentException(
                    "Properties file not found: " +
                    aPropFile.getPath() );
            }
        }
    }
