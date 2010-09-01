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
* Description:  Single CSS style rule
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.HashMap;

import org.w3c.css.sac.Selector;

/**
 * CSSRule contains one style rule parsed from CSS StyleSheet
 */
public class CSSRule implements Comparable
    {

    /** The selector. */
    private Selector iSelector;

    /** Style data for Selector */
    private HashMap iStyleMap;

    /** Is Rule pseudo rule */
    private boolean iPseudo;

    /** The specificity of the rule. */
    private CSSSpecificity iSpecificity;

    /**
     * Instantiates a new CSS rule.
     *
     * @param aSelector Selector parsed from CSS file
     * @param aStyleMap Style data for Selector
     */
    public CSSRule( Selector aSelector, HashMap aStyleMap )
        {
        iSelector = aSelector;
        iStyleMap = aStyleMap;
        iSpecificity = new CSSSpecificity();

        if ( CSSSelectorParser.isPseudo( iSelector ) )
            {
            iPseudo = true;
            }
        else
            {
            iPseudo = false;
            }

        }

    /**
     * Gets the selector.
     *
     * @return the selector
     */
    public Selector getSelector()
        {
        return iSelector;
        }

    /**
     * Checks if rule has pseudo condition.
     *
     * @return true, if is pseudo
     */
    public boolean isPseudo()
        {
        return iPseudo;
        }

    /**
     * Gets the specificity.
     *
     * @return the specificity
     */
    public CSSSpecificity getSpecificity()
        {
        return iSpecificity;
        }

    /**
     * Reset specificity.
     */
    public void resetSpecificity()
        {
        iSpecificity.reset();
        }

    /**
     * Sets the specificity.
     *
     * @param aSpecificity the new specificity
     */
    public void setSpecificity( CSSSpecificity aSpecificity )
        {
        iSpecificity = aSpecificity;
        }

    /**
     * Gets the style map.
     *
     * @return the style map
     */
    public HashMap getStyleMap()
        {
        return iStyleMap;
        }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    public int compareTo( Object aRule )
        {
        return iSpecificity.compare( ( ( CSSRule ) aRule ).getSpecificity() );
        }
    }
