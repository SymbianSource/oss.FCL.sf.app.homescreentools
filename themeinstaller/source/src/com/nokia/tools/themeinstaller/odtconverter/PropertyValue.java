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
* Description:  Single property value for property value list.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.awt.Color;
import java.io.IOException;

/**
 * Property value stores style related data before it is externalized
 * to a binary format.
 */
public class PropertyValue
    {

    // CONSTANTS
    // Ident types
    public static final String STRING_AUTO = "auto";
    public static final String STRING_NONE = "none";
    public static final String STRING_INHERIT = "inherit";

    public static final int E_NOT_SET = 0;
    public static final int E_AUTO = 1;
    public static final int E_NONE = 2;
    public static final int E_INHERIT = 3;

    // Property value type
    private Short iValueType;

    // Flag to identify ident
    private int iIdentType;

    // Rgb color value
    private Color iRgbValue;

    // Real value
    private double iRealValue;

    // String pool index to a string value
    private int iStringRef;

    // Reference to the String Pool
    private StringPool iStringPool;

    /**
     * Constructor.
     * @param aStringPool Reference to the String Pool
     */
    public PropertyValue( StringPool aStringPool )
        {
        iStringPool = aStringPool;
        }

    /**
     * Set rgb value.
     * @param aRgbValue the value to set
     * @param aValueType primitive value type
     * @throws ODTException
     * @throws ODTException if primitive value type is not a rgb color type
     */
    public void setRgbValue( Color aRgbValue )
        throws ODTException
        {
        iRgbValue = aRgbValue;
        iValueType = new Short( ValueTypeResolver.E_RGB_COLOR );
        }

    /**
     * Set real value.
     * @param aRealValue the value to set
     * @param aValueType primitive value type
     * @throws ODTException if primitive value type is not a real value type
     */
    public void setRealValue( double aRealValue, short aValueType )
        throws ODTException
        {
        // Verify the value type
        switch( aValueType )
            {
            case ValueTypeResolver.E_NUMBER:
            case ValueTypeResolver.E_PERCENTAGE:
            case ValueTypeResolver.E_EMS:
            case ValueTypeResolver.E_EXS:
            case ValueTypeResolver.E_PX:
            case ValueTypeResolver.E_CM:
            case ValueTypeResolver.E_MM:
            case ValueTypeResolver.E_IN:
            case ValueTypeResolver.E_PT:
            case ValueTypeResolver.E_PC:
            case ValueTypeResolver.E_DEG:
            case ValueTypeResolver.E_RAD:
            case ValueTypeResolver.E_GRAD:
            case ValueTypeResolver.E_MS:
            case ValueTypeResolver.E_S:
            case ValueTypeResolver.E_HZ:
            case ValueTypeResolver.E_KHZ:
            case ValueTypeResolver.E_UNIT_VALUE:
            break;

            default:
                throw new ODTException(
                        "Property value type is not compatible with real: "
                        + aValueType );
            }

        iRealValue = aRealValue;
        iValueType = new Short( aValueType );
        }

    /**
     * Set string value.
     * @param aString the string to set
     * @param aValueType primitive value type
     * @throws ODTException if primitive value type is not a string type
     */
    public void setString( String aString, short aValueType )
        throws ODTException
        {
        // Verify the value type
        switch( aValueType )
            {
            case ValueTypeResolver.E_STRING:
            case ValueTypeResolver.E_IDENT:
            case ValueTypeResolver.E_URI:
            case ValueTypeResolver.E_ATTR:
            case ValueTypeResolver.E_UNKNOWN:
            break;

            default:
                throw new ODTException(
                        "Property value type is not compatible with string: "
                        + aValueType );
            }

        // Add string to the pool
        iStringRef = iStringPool.addString( aString );

        // Resolve ident type
        if ( aString.equals( STRING_AUTO ) )
            {
            iIdentType = E_AUTO;
            }
        else if ( aString.equals( STRING_INHERIT ) )
            {
            iIdentType = E_INHERIT;
            }
        else if ( aString.equals( STRING_NONE ) )
            {
            iIdentType = E_NONE;
            }
        else
            {
            iIdentType = E_NOT_SET;
            }
        iValueType = new Short( aValueType );
        }

    /**
     * Externalize the property value to a stream.
     * @param aStream stream to use for externalization
     * @throws IOException if writing to a stream fails
     * @throws ODTException if value type can not be resolved
     */
    public void externalize( ODTDataOutputStream aStream )
        throws IOException, ODTException
        {
        // Write property value type - int8
        aStream.writeByte( iValueType.byteValue() );

        // Write property value data - real/int16/rgb
        switch( iValueType.intValue() )
            {
            // Real value
            case ValueTypeResolver.E_NUMBER:
            case ValueTypeResolver.E_PERCENTAGE:
            case ValueTypeResolver.E_EMS:
            case ValueTypeResolver.E_EXS:
            case ValueTypeResolver.E_PX:
            case ValueTypeResolver.E_CM:
            case ValueTypeResolver.E_MM:
            case ValueTypeResolver.E_IN:
            case ValueTypeResolver.E_PT:
            case ValueTypeResolver.E_PC:
            case ValueTypeResolver.E_DEG:
            case ValueTypeResolver.E_RAD:
            case ValueTypeResolver.E_GRAD:
            case ValueTypeResolver.E_MS:
            case ValueTypeResolver.E_S:
            case ValueTypeResolver.E_HZ:
            case ValueTypeResolver.E_KHZ:
            case ValueTypeResolver.E_UNIT_VALUE:
                aStream.writeTReal64( iRealValue );
            break;

            // String value and ident type
            case ValueTypeResolver.E_STRING:
            case ValueTypeResolver.E_IDENT:
            case ValueTypeResolver.E_URI:
            case ValueTypeResolver.E_ATTR:
            case ValueTypeResolver.E_UNKNOWN:
                aStream.writeInt16( iStringRef );
                aStream.writeByte( iIdentType );
            break;

            // Rgb value
            case ValueTypeResolver.E_RGB_COLOR:
                aStream.writeByte( iRgbValue.getRed() );
                aStream.writeByte( iRgbValue.getGreen() );
                aStream.writeByte( iRgbValue.getBlue() );
                break;
            default:
                throw new ODTException( "Property value can not be resolved: "
                        + iValueType );
            }

        }

    }
