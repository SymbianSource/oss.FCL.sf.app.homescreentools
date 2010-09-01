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
* Description:  Pseudo class resolver for CSS Style properties
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Hashtable;

/**
 * Resolves pseudo class values by keys.
 */
public class PseudoClassResolver
    { 

    // Pseudo class keys
    public static final int UNKNOWN       = -1;
    public static final int NONE          = 0;
    public static final int FOCUS         = 1;
    public static final int PASSIVE_FOCUS = 2;
    public static final int ACTIVE        = 3;
    public static final int HOLD          = 4;
    public static final int ENABLED       = 5;
    public static final int DISABLED      = 6;
    public static final int HOVER         = 7;
    public static final int LINK          = 8;
    public static final int VISITED       = 9;
    public static final int EDIT       = 10;

    // Pseudo class values
    private static final String NONE_VALUE          = "none";
    private static final String FOCUS_VALUE         = "focus";
    private static final String PASSIVE_FOCUS_VALUE = "passivefocus";
    private static final String ACTIVE_VALUE        = "active";
    private static final String HOLD_VALUE          = "hold";
    private static final String ENABLED_VALUE       = "enabled";
    private static final String DISABLED_VALUE      = "disabled";
    private static final String HOVER_VALUE         = "hover";
    private static final String LINK_VALUE          = "link";
    private static final String VISITED_VALUE       = "visited";
    private static final String EDIT_VALUE       = "edit";

    private Hashtable iPseudoClassTable;

    /**
     * Constructor.
     */
    public PseudoClassResolver()
        {
        iPseudoClassTable = new Hashtable();
        iPseudoClassTable.put( new Integer( NONE ), NONE_VALUE );
        iPseudoClassTable.put( new Integer( FOCUS ), FOCUS_VALUE );
        iPseudoClassTable.put( new Integer( PASSIVE_FOCUS ), PASSIVE_FOCUS_VALUE );
        iPseudoClassTable.put( new Integer( ACTIVE ), ACTIVE_VALUE );
        iPseudoClassTable.put( new Integer( HOLD ), HOLD_VALUE );
        iPseudoClassTable.put( new Integer( ENABLED ), ENABLED_VALUE );
        iPseudoClassTable.put( new Integer( DISABLED ), DISABLED_VALUE );
        iPseudoClassTable.put( new Integer( HOVER ), HOVER_VALUE );
        iPseudoClassTable.put( new Integer( LINK ), LINK_VALUE );
        iPseudoClassTable.put( new Integer( VISITED ), VISITED_VALUE );
        iPseudoClassTable.put( new Integer( EDIT ), EDIT_VALUE );
        }

    /**
     * Get pseudo class value by its key.
     * @param aClassKey Pseudo class key, for example, FOCUS
     * @return Pseudo class value, for example, "focus". Returns null if
     * the value can not be resolved.
     */
    public String getValue( Integer aClassKey )
        {
        return ( String ) iPseudoClassTable.get( aClassKey );
        }

    /**
     * Get pseudo class key by its value.
     * @param aClassValue Pseudo class value, for example, "focus"
     * @return Pseudo class key, for example, FOCUS. Returns UNKNOWN if the
     * value can not be resolved.
     */
    public int getKey( String aClassValue )
        {
        int result = UNKNOWN;

        Enumeration keys = iPseudoClassTable.keys();
        while ( keys.hasMoreElements() )
            {
            int key = ( ( Integer ) keys.nextElement() ).intValue();
            if ( aClassValue.equals( getValue( new Integer( key ) ) ) )
                {
                result = key;
                break;
                }
            }

        return result;
        }

    /**
     * Gets the table of pseudo class values.
     *
     * @return The table
     */
    public Collection getPseudoTypes()
        {
        return iPseudoClassTable.values();
        }

    }
