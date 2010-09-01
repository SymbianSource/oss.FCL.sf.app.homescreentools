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
* Description:  Exception for ODT parsing operations
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

/**
 * The Class ODTException.
 */
public class ODTException extends Exception
    {

    // Default serial version UID
    private static final long serialVersionUID = 1L;

    /**
     * Instantiates a new ODT exception.
     *
     * @param aMessage the message
     */
    public ODTException( String aMessage )
        {
        super( aMessage );
        }

    }
