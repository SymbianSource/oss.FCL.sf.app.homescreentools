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
* Description:  Stores the information for Style rules priority
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

/**
 * The Class CSSSpecificity stores the information for Style rules priority
 */
public class CSSSpecificity
    {
    final public static int ID = 0;
    final public static int ATTRIBUTE = 1;
    final public static int ELEMENT = 2;

    /** Table for counting specificity occurrences. */
    private int[] iSpecificity = { 0, 0, 0 };

    /**
     * Increase id count.
     */
    public void incID()
        {
        ++iSpecificity[ ID ];
        }

    /**
     * Increase attribute count.
     */
    public void incAttribute()
        {
        ++iSpecificity[ ATTRIBUTE ];
        }

    /**
     * Increase element count.
     */
    public void incElement()
        {
        ++iSpecificity[ ELEMENT ];
        }

    /**
     * Gets the specificity table.
     *
     * @return the specificity
     */
    public int[] getSpecificity()
        {
        return iSpecificity;
        }

    /**
     * Reset the table.
     */
    public void reset()
        {
        iSpecificity[ ID ] = 0;
        iSpecificity[ ATTRIBUTE ] = 0;
        iSpecificity[ ELEMENT ] = 0;
        }

    /**
     * Compare for another specificity.
     *
     * Order for priorities (3 has the highest priority): 1. element 2. .class
     * 3. #id
     *
     * @param aSpecificity Specificity to be compared
     *
     * @return 0 if this is equal, -1 if this is less, +1 if this is greater.
     */
    public int compare( CSSSpecificity aSpecificity )
        {
        int difference;

        difference = iSpecificity[ ID ] - aSpecificity.iSpecificity[ ID ];
        if ( difference != 0 )
            {
            if ( difference < 0 )
                {
                return -1;
                }
            else
                {
                return 1;
                }
            }

        difference = iSpecificity[ ATTRIBUTE ]
                - aSpecificity.iSpecificity[ ATTRIBUTE ];
        if ( difference != 0 )
            {
            if ( difference < 0 )
                {
                return -1;
                }
            else
                {
                return 1;
                }
            }

        difference = iSpecificity[ ELEMENT ]
                - aSpecificity.iSpecificity[ ELEMENT ];
        if ( difference != 0 )
            {
            if ( difference < 0 )
                {
                return -1;
                }
            else
                {
                return 1;
                }
            }

        return 0;
        }

    }
