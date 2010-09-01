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
* Description:  Parses SAC selector to find out its selector type
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import org.w3c.css.sac.CSSException;
import org.w3c.css.sac.CombinatorCondition;
import org.w3c.css.sac.Condition;
import org.w3c.css.sac.ConditionalSelector;
import org.w3c.css.sac.DescendantSelector;
import org.w3c.css.sac.Selector;

/**
 * Parses SAC Selector in order to find out if selector has pseudo condition.

 * For example selector "element.class:pseudo" is recognized as Conditional
 * Selector and the Selector's condition is ".class:pseudo" is recognized as
 * SAC_AND_CONDITION.
 *
 * After SAC_AND_CONDITION is parsed to two different conditions : ".class" and
 * ":pseudo", it is possible to tell that the original selector is Pseudo
 * Selector
 *
 */
public class CSSSelectorParser
    {

    /**
     * Checks if Selector is pseudo selector.
     *
     * @param aSelector The selector
     *
     * @return true, if is pseudo selector
     */
    public static boolean isPseudo( Selector aSelector )
        {
        switch ( aSelector.getSelectorType() )
            {
            case Selector.SAC_ELEMENT_NODE_SELECTOR:
                {
                return false;
                }
            case Selector.SAC_CONDITIONAL_SELECTOR:
                {
                ConditionalSelector cSelector = ( ConditionalSelector ) aSelector;
                return isPseudoCondition( cSelector.getCondition() );
                }
            case Selector.SAC_CHILD_SELECTOR:
                {
                DescendantSelector dSelector = ( DescendantSelector ) aSelector;
                return isPseudo( dSelector.getSimpleSelector() );
                }
            case Selector.SAC_DESCENDANT_SELECTOR:
                {
                DescendantSelector dSelector = ( DescendantSelector ) aSelector;
                return isPseudo( dSelector.getSimpleSelector() );
                }
            case Selector.SAC_ANY_NODE_SELECTOR:
            case Selector.SAC_DIRECT_ADJACENT_SELECTOR:
            case Selector.SAC_CDATA_SECTION_NODE_SELECTOR:
            case Selector.SAC_COMMENT_NODE_SELECTOR:
            case Selector.SAC_NEGATIVE_SELECTOR:
            case Selector.SAC_PROCESSING_INSTRUCTION_NODE_SELECTOR:
            case Selector.SAC_PSEUDO_ELEMENT_SELECTOR:
            case Selector.SAC_ROOT_NODE_SELECTOR:
            case Selector.SAC_TEXT_NODE_SELECTOR:
                {
                throw new CSSException( "Selector : "
                        + aSelector.getSelectorType() + " not supported" );
                }
            default:
                throw new CSSException( "Unknown selector : "
                        + aSelector.getSelectorType() );
            }
        }

    /**
     * Checks if SAC Condition is pseudo condition.
     *
     * @param aCondition The condition
     *
     * @return true, if is pseudo condition
     */
    private static boolean isPseudoCondition( Condition aCondition )
        {
        switch ( aCondition.getConditionType() )
            {
            case Condition.SAC_ID_CONDITION:
                {
                return false;
                }
            case Condition.SAC_CLASS_CONDITION:
                {
                return false;
                }
            case Condition.SAC_AND_CONDITION:
                {
                CombinatorCondition combCondition = ( CombinatorCondition ) aCondition;
                return isPseudoCondition( combCondition.getFirstCondition() )
                        || isPseudoCondition( combCondition
                                .getSecondCondition() );
                }
            case Condition.SAC_PSEUDO_CLASS_CONDITION:
                {
                return true;
                }
            case Condition.SAC_ATTRIBUTE_CONDITION:
            case Condition.SAC_ONE_OF_ATTRIBUTE_CONDITION:
            case Condition.SAC_BEGIN_HYPHEN_ATTRIBUTE_CONDITION:
            case Condition.SAC_OR_CONDITION:
            case Condition.SAC_NEGATIVE_CONDITION:
            case Condition.SAC_POSITIONAL_CONDITION:
            case Condition.SAC_LANG_CONDITION:
            case Condition.SAC_ONLY_CHILD_CONDITION:
            case Condition.SAC_ONLY_TYPE_CONDITION:
            case Condition.SAC_CONTENT_CONDITION:
                {
                throw new CSSException( "condition : "
                        + aCondition.getConditionType() + " not supported" );

                }
            default:
                throw new CSSException( "Unknown condition : "
                        + aCondition.getConditionType() );
            }
        }
    }
