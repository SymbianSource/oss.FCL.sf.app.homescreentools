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
* Description:  Primitive value type resolver for CSS Style properties
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.util.Hashtable;

import org.w3c.css.sac.LexicalUnit;

/**
 * Resolves primitive value types by keys.
 * Property types that are taken into account are
 * from Symbian side: ...\epoc32\include\middleware\xndompropertyvalue.h
 */
public class ValueTypeResolver
    {

    // CONSTANTS
    // Primitive Value Types
    public static final short E_UNKNOWN = 0;
    public static final short E_NUMBER = 1;
    public static final short E_PERCENTAGE = 2;
    public static final short E_EMS = 3;
    public static final short E_EXS = 4;
    public static final short E_PX = 5;
    public static final short E_CM = 6;
    public static final short E_MM = 7;
    public static final short E_IN = 8;
    public static final short E_PT = 9;
    public static final short E_PC = 10;
    public static final short E_DEG = 11;
    public static final short E_RAD = 12;
    public static final short E_GRAD = 13;
    public static final short E_MS = 14;
    public static final short E_S = 15;
    public static final short E_HZ = 16;
    public static final short E_KHZ = 17;
    public static final short E_STRING = 19;
    public static final short E_URI = 20;
    public static final short E_IDENT = 21;
    public static final short E_ATTR = 22;
    public static final short E_RGB_COLOR = 25;
    public static final short E_RGBA_COLOR = 26;
    public static final short E_UNIT_VALUE = 28;

    // Ident Types
    public static final short E_NOT_SET = 0;
    public static final short E_AUTO = 1;
    public static final short E_NONE = 2;
    public static final short E_INHERIT = 3;

    private Hashtable iValueTypeResolver;

    /**
     * Instantiates a new value type resolver.
     */
    public ValueTypeResolver()
        {
        iValueTypeResolver = new Hashtable();

        //Real Value Types
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_INTEGER ), new Short( E_NUMBER ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_REAL ), new Short( E_NUMBER ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_PERCENTAGE ), new Short( E_PERCENTAGE ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_EM ), new Short( E_EMS ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_EX ), new Short( E_EXS ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_PIXEL ), new Short( E_PX ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_CENTIMETER ), new Short( E_CM ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_MILLIMETER ), new Short( E_MM ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_INCH ), new Short( E_IN ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_POINT ), new Short( E_PT ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_PICA ), new Short( E_PC ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_DEGREE ), new Short( E_DEG ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_RADIAN ), new Short( E_RAD ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_GRADIAN ), new Short( E_GRAD ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_MILLISECOND ), new Short( E_MS ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_SECOND ), new Short( E_S ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_HERTZ ), new Short( E_HZ ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_KILOHERTZ ), new Short( E_KHZ ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_DIMENSION ), new Short( E_UNIT_VALUE ));

        //String Value Types
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_STRING_VALUE ), new Short( E_STRING ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_IDENT ), new Short( E_IDENT ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_URI ), new Short( E_URI ));
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_ATTR ), new Short( E_ATTR ));

        //Color value Types
        iValueTypeResolver.put( new Short( LexicalUnit.SAC_RGBCOLOR ), new Short( E_RGB_COLOR ));

        }

    /**
     * Gets the value of the Symbian specific code for value type.
     *
     * @param aKey The key for Lexical Unit
     *
     * @return the The value of the Symbian specific code
     */
    public Short getValue( Short aKey )
        {
        if ( iValueTypeResolver.containsKey( aKey ) )
            {
            return ( Short ) iValueTypeResolver.get( aKey );
            }
        else
            throw new IllegalStateException(
                    "Invalid value type while resolving CSS : " + aKey );
        }

    }
