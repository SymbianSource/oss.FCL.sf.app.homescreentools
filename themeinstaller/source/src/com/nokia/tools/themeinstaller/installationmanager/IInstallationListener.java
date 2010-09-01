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
* Description:  This class is interface for ODT installation
 *
*/

package com.nokia.tools.themeinstaller.installationmanager;

public interface IInstallationListener
    {

    // CONSTANTS
    // Installation states
    public static final int STATE_PARSED = 1;
    public static final int STATE_WRITED = 2;
    public static final int NO_ERROR = 0;
    public static final int ERROR = -1;

    /**
     * Called when installation has progressed
     * @param aEvent Progress event
     */
    public void installationProgress( ProgressEvent aEvent );

    /**
     * Called when installation is finished
     * @param aEvent Progress event
     */
    public void installationCompleted( ProgressEvent aEvent );

    }
