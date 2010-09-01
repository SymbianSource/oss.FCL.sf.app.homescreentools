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
* Description:  CSS Style property value
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

/**
 * Contains property's value and value type
 */
public class CSSPropertyValue
    {

    /** The Constant STRING_SEPARATOR. */
    private static final String STRING_SEPARATOR = "|";

    /** The value as string. */
    private String iValue;

    /** The value type. */
    private short iValueType;

    /**
     * Instantiates a new CSS property value.
     *
     * @param aValue the a value
     * @param aValueType the a value type
     */
    public CSSPropertyValue( short aValueType, String aValue )
        {
        iValue = aValue;
        iValueType = aValueType;
        }

    /**
     * Gets the value.
     *
     * @return the value
     */
    public String getValue()
        {
        return iValue;
        }

    /**
     * Gets the value type.
     *
     * @return the value type
     */
    public short getValueType()
        {
        return iValueType;
        }

    /**
     * Gets the value type as string.
     *
     * @return the value type as string
     */
    public String getValueTypeAsString()
        {
        return String.valueOf( iValueType );
        }

    /**
     * Gets the value type and value.
     *
     * @return the value type and value
     */
    public String getValueTypeAndValue()
        {
        return iValueType + STRING_SEPARATOR + iValue;
        }

    }
