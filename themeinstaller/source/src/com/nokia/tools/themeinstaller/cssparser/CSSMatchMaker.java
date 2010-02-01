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
* Description:  Compares W3C DOM Elements and CSS Selectors
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.Collection;
import java.util.Iterator;

import org.w3c.css.sac.AttributeCondition;
import org.w3c.css.sac.CSSException;
import org.w3c.css.sac.CombinatorCondition;
import org.w3c.css.sac.Condition;
import org.w3c.css.sac.ConditionalSelector;
import org.w3c.css.sac.DescendantSelector;
import org.w3c.css.sac.ElementSelector;
import org.w3c.css.sac.Selector;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

/**
 * The Class CSSMatchMaker compares W3C DOM Elements and CSS Selectors. Match
 * method returns true if CSS Selector has style rules for the given DOM Element
 */
public class CSSMatchMaker
    {

    /** The Constant STRING_CLASS. */
    private static final String STRING_CLASS = "class";

    /** The Constant STRING_ID. */
    private static final String STRING_ID = "id";

    /** The Constant STRING_SPACE. */
    private static final String STRING_SPACE = " ";

    /** The pseudo class resolver. */
    private PseudoClassResolver iPseudoClassResolver;

    /**
     * Instantiates a new CSS Match Maker.
     */
    public CSSMatchMaker()
        {
        iPseudoClassResolver = new PseudoClassResolver();
        }

    /**
     * Compares if CSS rule with it's selector has style instructions for given
     * DOM Element.
     *
     * @param aElement W3C DOM Element
     * @param aRule The style rule
     *
     * @return true, if CSS Selector matches DOM Element
     */
    public boolean match( CSSRule aRule, Element aElement ){
        aRule.resetSpecificity();
        return match( aRule.getSelector(), aRule.getSpecificity(), aElement );

    }

    /**
     * Compares if CSS rule's selector has style instructions for given DOM
     * Element.
     *
     * @param aSelector the a selector
     * @param aSpecificity CSSRules specificity table to be updated during the
     *            comparison
     * @param aElement the a element
     *
     * @return true, if given selector match DOM Element
     */
    private boolean match( Selector aSelector, CSSSpecificity aSpecificity, Element aElement )
        {
        switch ( aSelector.getSelectorType() )
            {
            case Selector.SAC_ELEMENT_NODE_SELECTOR:
                {
                ElementSelector eSelector = ( ElementSelector ) aSelector;
                String name = eSelector.getLocalName();
//                if("box".equals(aElement.getLocalName())&& "box".equals(name) ){
//                	System.out.println("!!!");
//                }
                if ( name == null || name.equals( aElement.getLocalName() ) )
                    {
                    aSpecificity.incElement();
                    return true;
                    }
                return false;
                }

            case Selector.SAC_CONDITIONAL_SELECTOR:
                {
                ConditionalSelector cSelector = ( ConditionalSelector ) aSelector;
                if ( !match( cSelector.getSimpleSelector(), aSpecificity,
                        aElement ) )
                    {
                    return false;
                    }
                return matchCondition( cSelector.getCondition(), aSpecificity,
                        aElement );
                }

            case Selector.SAC_CHILD_SELECTOR:
                {
                DescendantSelector dSelector = ( DescendantSelector ) aSelector;
                if ( !match( dSelector.getSimpleSelector(), aSpecificity,
                        aElement ) )
                    {
                    return false;
                    }
                return match( dSelector.getAncestorSelector(), aSpecificity,
                        ( Element ) aElement.getParentNode() );
                }
            case Selector.SAC_DESCENDANT_SELECTOR:
                {
                DescendantSelector dSelector = ( DescendantSelector ) aSelector;
                if ( !match( dSelector.getSimpleSelector(), aSpecificity,
                        aElement ) )
                    {
                    return false;
                    }

                Node ancestor = aElement;
                while ( ( ancestor = ancestor.getParentNode() ) != null )
                    {
                    if ( ancestor.getNodeType() == Node.ELEMENT_NODE )
                        {
                        if ( match( dSelector.getAncestorSelector(),
                                aSpecificity, ( Element ) ancestor ) )
                            {
                            return true;
                            }
                        }
                    }
                return false;
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
     * For Conditional Selectors, it is also necessary to check if selectors
     * conditions match with the DOM Element.
     *
     * @param aCondition The condition of the conditional selector
     * @param aElement The DOM element
     * @param aSpecificity CSSRules specificity table to be updated during the
     *            comparison
     *
     * @return true, if given Condition match DOM Element
     */
    private boolean matchCondition( Condition aCondition,
            CSSSpecificity aSpecificity, Element aElement )
        {
        switch ( aCondition.getConditionType() )
            {
            case Condition.SAC_ID_CONDITION:
                {
                AttributeCondition idCondition = ( AttributeCondition ) aCondition;
                String idAttribute = aElement.getAttribute( STRING_ID );

                String[] idTexts = idAttribute.split( STRING_SPACE );

                for ( int i = 0; i < idTexts.length; i++ )
                    {
                    String idText = idTexts[ i ];
                    if ( idAttribute != null
                            && idText.equals( idCondition.getValue() ) )
                        {
                        aSpecificity.incID();
                        return true;
                        }
                    }
                return false;
                }

            case Condition.SAC_CLASS_CONDITION:
                {
                AttributeCondition classCondition = ( AttributeCondition ) aCondition;
                String classAttribute = aElement.getAttribute( STRING_CLASS );

                String[] classTexts = classAttribute.split( STRING_SPACE );

                for ( int i = 0; i < classTexts.length; i++ )
                    {
                    String classText = classTexts[ i ];
                    if ( classAttribute != null
                            && classText.equals( classCondition.getValue() ) )
                        {
                        aSpecificity.incAttribute();
                        return true;
                        }
                    }
                return false;
                }

            case Condition.SAC_AND_CONDITION:
                {
                CombinatorCondition combCondition = ( CombinatorCondition ) aCondition;
                return matchCondition( combCondition.getFirstCondition(),
                        aSpecificity, aElement )
                        && matchCondition( combCondition.getSecondCondition(),
                                aSpecificity, aElement );
                }

            case Condition.SAC_PSEUDO_CLASS_CONDITION:
                {
                Collection pseudoTypes = iPseudoClassResolver
                        .getPseudoTypes();

                for ( Iterator it = pseudoTypes.iterator(); it
                        .hasNext(); )
                    {
                    if ( it.next()
                            .equals( aCondition.toString().substring( 1 ) ) )
                        {
                        aSpecificity.incAttribute();
                        return true;
                        }
                    }
                return false;
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
