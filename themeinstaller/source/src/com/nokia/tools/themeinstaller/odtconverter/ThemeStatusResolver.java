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
* Description:  Theme status flag-definition resolver
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.util.Hashtable;

/**
 * Resolver for theme status flag-definition.
 * Theme status flag-definitions are taken from Xuikon XnThemeManagement.h
 */
public class ThemeStatusResolver
    {
    // Theme status flag-definitions. Theme status flags are bit-masked.

    // Theme has no specific status. This is a common case.
    // 0b0000000000000000
    public static final int E_XN_THEME_STATUS_NONE = 0x0000;

    // EXnThemeStatusLicenceeDefault.
    // This theme is licencee default. It is located on ROM (Z-drive)
    // 0b0000000000000010
    public static final int E_XN_THEME_STATUS_LICENCEE_DEFAULT = 0x0002;

    // EXnThemeStatusOperatorDefault. This theme is set as operator default.
    // 0b0000000000000100
    public static final int E_XN_THEME_STATUS_OPERATOR_DEFAULT = 0x0004;

    // EXnThemeStatusUserDefault. This theme has set as user default.
    // 0b0000000000001000
    public static final int E_XN_THEME_STATUS_USER_DEFAULT = 0x0008;

    // EXnThemeStatusMakeActive. Activates the theme after installation.
    // 0b0000000000010000
    public static final int E_XN_THEME_STATUS_MAKE_ACTIVE = 0x0010;

    // EXnThemeStatusLicenceeRestorable. This theme is restored when licensee
    // default theme is restored. When using this flag, the
    // ThemeStatusLicenceeDefault-flag is also automatically activated.
    // It is located on ROM (Z-drive)
    // 0b00000000001000000
    public static final int E_XN_THEME_STATUS_LICENCEE_RESTORABLE = 0x0040;

    // EXnThemeStatusLocked.
    // 0b00000000010000000
    public static final int E_XN_THEME_STATUS_LOCKED = 0x0080;

    // Theme status keys
    public static final String THEME_STATUS_NONE = "ThemeStatusNone";
    public static final String THEME_STATUS_LOCKED = "ThemeStatusLocked";
    public static final String THEME_STATUS_MAKE_ACTIVE = "ThemeStatusMakeActive";
    public static final String THEME_STATUS_LICENCEE_DEFAULT = "ThemeStatusLicenceeDefault";
    public static final String THEME_STATUS_LICENCEE_RESTORABLE = "ThemeStatusLicenceeRestorable";
    public static final String THEME_STATUS_OPERATOR_DEFAULT = "ThemeStatusOperatorDefault";
    public static final String THEME_STATUS_USER_DEFAULT = "ThemeStatusUserDefault";

    private static Hashtable iThemeStatusResolver;
    static
        {
        iThemeStatusResolver = new Hashtable();

        iThemeStatusResolver.put( THEME_STATUS_NONE, new Integer(
                E_XN_THEME_STATUS_NONE ) );
        iThemeStatusResolver.put( THEME_STATUS_LICENCEE_DEFAULT, new Integer(
                E_XN_THEME_STATUS_LICENCEE_DEFAULT ) );
        iThemeStatusResolver.put( THEME_STATUS_OPERATOR_DEFAULT, new Integer(
                E_XN_THEME_STATUS_OPERATOR_DEFAULT ) );
        iThemeStatusResolver.put( THEME_STATUS_USER_DEFAULT, new Integer(
                E_XN_THEME_STATUS_USER_DEFAULT ) );
        iThemeStatusResolver.put( THEME_STATUS_MAKE_ACTIVE, new Integer(
                E_XN_THEME_STATUS_MAKE_ACTIVE ) );
        iThemeStatusResolver.put( THEME_STATUS_LICENCEE_RESTORABLE,
                new Integer( E_XN_THEME_STATUS_LICENCEE_RESTORABLE ) );
        iThemeStatusResolver.put( THEME_STATUS_LOCKED, new Integer(
                E_XN_THEME_STATUS_LOCKED ) );
        }

    private ThemeStatusResolver()
        {
        }

    /**
     * Gets the flag definition of the theme status.
     *
     * @param aKey theme status
     *
     * @return the The flag definition of the theme status
     * @throws IllegalArgumentException if the key is not mapped to any
     *                                  value in iThemeStatusResolver
     */
    public static Integer getValue( String aKey ) throws IllegalArgumentException
        {
        if( !iThemeStatusResolver.containsKey( aKey ) )
            {
            throw new IllegalArgumentException( "Invalid theme status" );
            }

        return  ( Integer ) iThemeStatusResolver.get( aKey );
        }
    }
