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
* Description:  Interface for localisation enhancements
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.io.File;
import java.io.IOException;

/**
 * Interface for localisation enhancements.
 */
public interface ILocalisation
    {

    /**
     * Get localisation settings of the theme.
     * @return Localisation settings
     */
    public Settings getSettings();

    /**
     * Find and compose a DTD file according to the provided localisation
     * settings. The temp-DTD file is deleted in the JVM exit.
     * @param aFileName Main dtd file name
     * @param aLanguage Language id of the language install
     * @return The composed DTD-file containing the main DTD file and
     * the extra entities from other DTD-files.
     * @throws IOException if reading/writing from/to DTD files fail.
     */
    public File composeDTD( String aFileName, int aLanguage ) throws IOException;

    /**
     * Find a DTD file according to the provided localisation settings.
     * @param aFileName DTD file name
     * @return The DTD file
     * @throws IOException if reading DTD files fail.
     */
    public File findDTD( String aFileName ) throws IOException;

    }
