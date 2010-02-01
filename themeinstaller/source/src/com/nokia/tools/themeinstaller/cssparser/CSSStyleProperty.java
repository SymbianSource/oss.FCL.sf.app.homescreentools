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
* Description:  CSS Style property
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.Vector;

/**
 * Contains information for style value.
 */
public class CSSStyleProperty
    {

    /** Property values. */
    private Vector iValues;

    /** Information whether Style property is categorized as important. */
    private boolean iImportant;

    /**
     * Instantiates a new CSS style property.
     *
     * @param aValues property values
     * @param aImportant Is property important
     */
    public CSSStyleProperty( Vector aValues, boolean aImportant )
        {
        iValues = aValues;
        iImportant = aImportant;
        }

    /**
     * Gets the values.
     *
     * @return the values
     */
    public Vector getValues()
        {
        return iValues;
        }

    /**
     * Checks if property is important.
     *
     * @return true, if is important
     */
    public boolean isImportant()
        {
        return iImportant;
        }

    }
