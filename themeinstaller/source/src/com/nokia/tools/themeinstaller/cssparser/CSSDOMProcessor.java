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
* Description:  CSSDOMProcessor applies given CSSRules to DOM Document.
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import org.w3c.css.sac.LexicalUnit;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.traversal.DocumentTraversal;
import org.w3c.dom.traversal.NodeFilter;
import org.w3c.dom.traversal.NodeIterator;

/**
 * CSSDOMProcessor applies given CSSRules to DOM Document.
 */
public class CSSDOMProcessor
    {
    /** The Constant STRING_PROPERTY. */
    public static final String STRING_PROPERTY = "styleproperty";

    /** The Constant STRING_PSEUDOCLASS. */
    public static final String STRING_PSEUDOCLASS = "pseudoclass";

    /** The Constant STRING_NAME. */
    public static final String STRING_NAME = "name";

    /** The Constant STRING_VALUE. */
    public static final String STRING_VALUE = "value";

    /** The Constant STRING_INHERIT. */
    public static final String STRING_INHERIT = "inherit";

    /** The Constant CHAR_COLON. */
    private static final char CHAR_COLON = ':';

    /** The Constant STRING_SEPARATOR. */
    private static final String STRING_SEPARATOR = "|";

    /** The Constant PSEUDO_TABLE. */
    private static final String[] UNSTYLABLE_ELEMENTS_TABLE = { "styleproperty" };

    /** The Element type resolver. */
    private static ElementTypeResolver iElementTypeResolver = new ElementTypeResolver();

    /** The Constant INHERITABLE_PROPERTIES. */
    public static final String[] INHERITABLE_PROPERTIES = { "visibility",
            "block-progression", "direction", "color", "font-family",
            "font-size", "font-weight", "font-style", "_s60-tab-style",
            "_s60-tab-color" };

    /** The Match Maker. */
    private CSSMatchMaker iCSSMatchMaker;

    /**
     * Instantiates a new CSSDOM processor.
     */
    public CSSDOMProcessor()
        {
        iCSSMatchMaker = new CSSMatchMaker();
        }

    /**
     * Sort rules.
     *
     * @param rules The rules to be sorted by priority
     */
    private static void sortRules( Vector rules )
        {
        Collections.sort( rules );
        }

    /**
     * Checks if is stylable element.
     *
     * @param aElement The element to be checked
     *
     * @return true, if is stylable element
     */
    private static boolean isStylableElement(Element aElement){

    for ( int i = 0; i < UNSTYLABLE_ELEMENTS_TABLE.length; i++ )
        {
        if ( UNSTYLABLE_ELEMENTS_TABLE[ i ].equals( aElement.getTagName() ))
            {
            return false;
            }
        }

        return true;
    }

    /**
     * Apply style rule to DOM. Walks through the DOM tree elements and finds
     * those that match with the CSSRule Selector. If matching element is found,
     * Rule is applied to DOM Element.
     *
     * @param aDocument The DOM document to apply the rules
     * @param aRuleList List of CSS style rules
     */
    public void applyRulesToDom( Document aDocument,
            Vector aRuleList )
        {
        DocumentTraversal traversal = ( DocumentTraversal ) aDocument;

        NodeIterator iterator = traversal.createNodeIterator( aDocument
                .getDocumentElement(), NodeFilter.SHOW_ELEMENT, null, true );

        for ( Node node = iterator.nextNode(); node != null; node = iterator
                .nextNode() )
            {
            Element element = ( Element ) node;
                if ( isStylableElement(element) )
                {
                Vector rulesMatch = new Vector();

                for ( int i = 0; i < aRuleList.size(); i++ )
                    {
                	
                    CSSRule rule = ( CSSRule ) aRuleList.get( i );
                    
                    if ( iCSSMatchMaker.match( rule, element ) )
                        {
                        rulesMatch.add( rule );
                        }
                    }

                sortRules( rulesMatch );

                for ( int j = 0; j < rulesMatch.size(); j++ )
                    {
                    CSSRule matchingRule = ( CSSRule ) rulesMatch.elementAt( j );
//                    if(matchingRule.getSelector().toString().equals("box:edit")){
//                    	System.out.println("Party");
//                    }
                    
                    applyRuleToElement( element, matchingRule );
                    }
                }
            }
            applyInheritance( aDocument );
        }


    /**
     * Checks if given property is inheritable property.
     *
     * @param aProperty the a property
     *
     * @return true, if is inheritable property
     */
    public boolean isInheritableProperty( String aProperty )
        {
        for ( int i = 0; i < INHERITABLE_PROPERTIES.length; i++ )
            {
            if ( aProperty.equals( INHERITABLE_PROPERTIES[ i ] ) )
                {
                return true;
                }
            }
        return false;
        }

    /**
     * Checks if given element can inherit given property name.
     *
     * @param aElement the a element
     * @param aPropertyName the a value's name
     *
     * @return true, if element can inherit the property
     */
    public boolean canInherit( Element aElement, String aPropertyName )
        {
        return canInherit( aElement, aPropertyName, null );
        }

    /**
     * Checks if given element can inherit given property.
     *
     * If property value equals "inherit", the property
     * is interpreted as inherited.
     *
     * If property is inheritable and element can inherit
     * properties, the element can inherit the property.
     *
     * @param aElement the a element
     * @param aPropertyName the a property's name
     * @param aPropertyValue the a property's value
     *
     * @return true, if element can inherit the property
     */
    public boolean canInherit( Element aElement, String aPropertyName,
            String aPropertyValue )
        {
        if ( aPropertyValue != null && aPropertyValue.equals( STRING_INHERIT ) )
            {
            return true;
            }

        if ( !isInheritableProperty( aPropertyName ) )
            {
            return false;
            }

        if ( iElementTypeResolver.canInherit( aElement.getNodeName() ) )
            {
            return true;
            }

        return false;
        }

    /**
     * Apply inheritance for stylable nodes that can inherit properties from
     * parent elements.
     *
     * @param aDocument The DOM document to be modified
     */
    private void applyInheritance( Document aDocument )
        {
        DocumentTraversal traversal = ( DocumentTraversal ) aDocument;

        NodeIterator iterator = traversal.createNodeIterator( aDocument
                .getDocumentElement(), NodeFilter.SHOW_ELEMENT, null, true );

        for ( Node node = iterator.nextNode(); node != null; node = iterator
                .nextNode() )
            {
            Element element = ( Element ) node;
//            if(node.getLocalName().equals("box"))
//            		System.out.println("Kill me!!!");
            if ( isStylableElement( element ) )
                {
                if ( iElementTypeResolver.canInherit( element.getNodeName() ) )
                    {
                    applyInheritance( element );
                    }
                }
            }
        }

    /**
     * Apply inheritance for DOM Element. Checks if any of the elements parents
     * has properties that can be inherited in the given element. If such
     * property is found, new property to the element is added, unless there
     * already exists a property with the same name.
     *
     * @param aElement The element to be modified
     */
    private void applyInheritance( Element aElement )
        {
        for ( int i = 0; i < INHERITABLE_PROPERTIES.length; i++ )
            {
            String inheritableProperty = INHERITABLE_PROPERTIES[ i ];
            if ( iElementTypeResolver.canInherit( aElement.getNodeName() ) )
                {
                if ( !hasAttribute( aElement, inheritableProperty ) )
                    {
                    if ( hasParentElementWithAttribute( aElement,
                            inheritableProperty ) )
                        {
                        if ( hasChildElementWithAttribute( aElement,
                                STRING_PROPERTY, inheritableProperty ) == null )
                            {
                            addNewChildElement( aElement, STRING_PROPERTY,
                                    inheritableProperty,
                                    LexicalUnit.SAC_IDENT
                                            + STRING_SEPARATOR + STRING_INHERIT );
                            }
                        }
                    }
                }
            }
        }

    /**
     * Checks for parent element with attribute name.
     *
     * @param aElement The element that's parents are checked
     * @param aAttributeName The name of the property
     *
     * @return true, aElement has parent node with given attribute name
     */
    private static boolean hasParentElementWithAttribute( Element aElement,
            String aAttributeName )
        {
        Node n = aElement.getParentNode();
        while ( n != null )
            {
            if ( n.getNodeType() == Node.ELEMENT_NODE )
                {
                if ( hasChildElementWithAttribute( ( Element ) n,
                        STRING_PROPERTY, aAttributeName ) != null )
                    {
                    return true;
                    }
                }
            n = n.getParentNode();
            }
        return false;
        }

    /**
     * Apply rule to DOM Element. Creates child elements for aElement with style
     * data. If the element already has matching child element, the value of it
     * is overwritten.
     *
     * @param aElement The DOM Element
     * @param aRule CSS style rule
     */
    private void applyRuleToElement( Element aElement, CSSRule aRule )
        {
        HashMap styleMap = aRule.getStyleMap();

        Iterator itKeys = styleMap.keySet().iterator();
        while ( itKeys.hasNext() )
            {
            String keyName = ( String ) itKeys.next();

            // Case 1 : Rule has pseudo selector, add or replace Element
            if ( aRule.isPseudo() )
                {
                String selectorString = aRule.getSelector().toString();
                String pseudoPart = selectorString.substring( selectorString
                        .lastIndexOf( CHAR_COLON ) + 1 );

                Vector elementsAttributes = new Vector();
                elementsAttributes.add( new NameValuePair(STRING_NAME, keyName) );
                elementsAttributes.add( new NameValuePair(STRING_PSEUDOCLASS, pseudoPart) );

                Element e = hasChildElementWithAttributes( aElement,
                        STRING_PROPERTY, elementsAttributes );
                if ( e != null && hasAttribute( e, STRING_NAME, keyName ) )
                    {

                    CSSStyleProperty property = ( CSSStyleProperty ) styleMap
                            .get( keyName );
                    Vector values = property.getValues();

                    CSSPropertyValue propertyValue = ( CSSPropertyValue ) values
                            .elementAt( 0 );

                    // 1st value has name "value"
                    e.setAttribute( STRING_VALUE, propertyValue
                            .getValueTypeAndValue() );

                    // if there are more values, their name is set to "value1,
                    // value 2, ..."
                    for ( int i = 1; i < values.size(); i++ )
                        {

                        propertyValue = ( CSSPropertyValue ) values
                                .elementAt( i );

                        e.setAttribute( STRING_VALUE + i, propertyValue
                                .getValueTypeAndValue() );
                        }
                    }
                else
                    {

                    CSSStyleProperty property = ( CSSStyleProperty ) styleMap
                            .get( keyName );
                    Vector values = property.getValues();

                    CSSPropertyValue propertyValue = ( CSSPropertyValue ) values
                            .elementAt( 0 );

                    Element newElement = addNewChildElement( aElement,
                            STRING_PROPERTY, keyName, propertyValue
                                    .getValueTypeAndValue(), pseudoPart );

                    // Rest of the values are set to element we just created
                    for ( int i = 1; i < values.size(); i++ )
                        {
                        propertyValue = ( CSSPropertyValue ) values
                                .elementAt( i );
                        newElement.setAttribute( STRING_VALUE + i,
                                propertyValue.getValueTypeAndValue() );
                        }
                    }
                }
            // Case 2 : Rule don't have pseudo selector, add or replace Element
            else
                {
                Vector elementsAttributes = new Vector();
                elementsAttributes.add( new NameValuePair(STRING_NAME, keyName) );

                Element e = hasChildElementWithAttributes( aElement,
                        STRING_PROPERTY, elementsAttributes );

                if ( e != null && hasAttribute( e, STRING_NAME, keyName ) )
                    {
                    CSSStyleProperty property = ( CSSStyleProperty ) styleMap
                            .get( keyName );
                    Vector values = property.getValues();

                    CSSPropertyValue propertyValue = ( CSSPropertyValue ) values
                            .elementAt( 0 );

                    // 1st value has name "value"
                    e.setAttribute( STRING_VALUE, propertyValue
                            .getValueTypeAndValue() );

                    // if there are more values, their name is set to "value1,
                    // value 2, ..."
                    for ( int i = 1; i < values.size(); i++ )
                        {
                        propertyValue = ( CSSPropertyValue ) values
                                .elementAt( i );
                        e.setAttribute( STRING_VALUE + i, propertyValue
                                .getValueTypeAndValue() );
                        }
                    }
                else
                    {

                    CSSStyleProperty property = ( CSSStyleProperty ) styleMap
                            .get( keyName );
                    Vector values = property.getValues();

                    CSSPropertyValue propertyValue = ( CSSPropertyValue ) values
                            .elementAt( 0 );

                    Element newElement = addNewChildElement( aElement,
                            STRING_PROPERTY, keyName, propertyValue
                                    .getValueTypeAndValue() );

                    // Rest of the values are set to element we just created
                    for ( int i = 1; i < values.size(); i++ )
                        {
                        propertyValue = ( CSSPropertyValue ) values
                                .elementAt( i );
                        newElement.setAttribute( STRING_VALUE + i,
                                propertyValue.getValueTypeAndValue() );
                        }
                    }
                }
            }
        }

    /**
     * Checks if DOM Element has a attribute with given value.
     *
     * @param aElement The DOM element to check
     * @param aValue Attributes value
     *
     * @return true, if successful
     */
    private static boolean hasAttribute( Element aElement, String aValue )
        {
        return hasAttribute( aElement, null, aValue );
        }


    /**
     * Checks if DOM Element has a attribute with given name and value.
     * Attribute's name can be null, when only the attributes value is checked
     *
     * @param aElement The DOM element to check
     * @param aName Attributes name
     * @param aValue Attributes value
     *
     * @return true, if successful
     */
    private static boolean hasAttribute( Element aElement, String aName,
            String aValue )
        {
        if ( aElement == null )
            {
            return false;
            }
        if ( aElement.hasAttributes() )
            {
            NamedNodeMap nnm = aElement.getAttributes();
            for ( int i = 0; i < nnm.getLength(); i++ )
                {
                Node att = nnm.item( i );
                if ( aName != null )
                    {
                    if ( att.getNodeValue().equals( aValue )
                            && att.getNodeName().equals( aName ) )
                        {
                        return true;
                        }
                    }
                else
                    {
                    if ( att.getNodeValue().equals( aValue ) )
                        {
                        return true;
                        }
                    }
                }
            }
        return false;
        }

    /**
     * Checks for elements attributes.
     *
     * @param aElement The element to be checked
     * @param aAttributes Attributes in name-value pairs
     *
     * @return true, if element has attributes given in aAttributes
     */
    private static boolean hasAttributes( Element aElement, Vector aAttributes )
        {
        if ( aElement == null )
            {
            return false;
            }

        if ( aElement.hasAttributes() )
            {

            for ( int i = 0; i < aAttributes.size(); i++ )
                {

                NameValuePair nameValuePair = ( NameValuePair ) aAttributes
                        .get( i );

                String name = nameValuePair.getName();
                String value = nameValuePair.getValue();

                if ( !hasAttribute( aElement, name, value ) )
                    {
                    return false;
                    }
                }
            }
        return true;
        }

    /**
     * Checks for child element with attribute's name.
     *
     * @param aParent The parent element
     * @param aElementName The element tag name to be matched with child nodes
     *            name
     * @param aName Attributes name to be matched
     *
     * @return Child element with attribute, null if none
     */
    private static Element hasChildElementWithAttribute( Element aParent,
            String aElementName, String aName )
        {
        for ( Node n = aParent.getFirstChild(); n != null; n = n
                .getNextSibling() )
            {
            if ( n.getNodeType() == Node.ELEMENT_NODE )
                {
                if ( hasAttribute( ( Element ) n, aName )
                        && n.getNodeName().equals( aElementName ) )
                    {
                    return ( Element ) n;
                    }
                }
            }
        return null;
        }



    /**
     * Checks for child element with attributes.
     *
     * @param aParent The parent element
     * @param aElementName The element tag name to be matched with child nodes
     *            name
     * @param aNameValuePairs The Name-Value pairs for attributes that need to be
     *            found
     *
     * @return Child element with attributes, null if none
     */
    private static Element hasChildElementWithAttributes( Element aParent,
            String aElementName, Vector aNameValuePairs )
        {
        for ( Node n = aParent.getFirstChild(); n != null; n = n
                .getNextSibling() )
            {
            if ( n.getNodeType() == Node.ELEMENT_NODE )
                {
                if ( n.getNodeName().equals( aElementName )
                        && hasAttributes( ( Element ) n, aNameValuePairs ) )
                    {
                    return ( Element ) n;
                    }
                }
            }
        return null;
        }

    /**
     * Adds the new node to DOM.
     *
     * @param aParent The parent of the new node
     * @param aElementName Element name for new DOM node
     * @param aKeyName Attribute name for new DOM node
     * @param aKeyValue Attribute value for new DOM node
     */
    private Element addNewChildElement( Element aParent,
            String aElementName, String aKeyName, String aKeyValue )
        {
        return addNewChildElement( aParent, aElementName, aKeyName, aKeyValue, null );
        }

    /**
     * Adds the new node to DOM.
     *
     * @param aParent The parent of the new node
     * @param aElementName Element name for new DOM node
     * @param aKeyName Attribute name for new DOM node
     * @param aKeyValue Attribute value for new DOM node
     * @param aPseudo Pseudo attribute value for the DOM node
     */
    private Element addNewChildElement( Element aParent, String aElementName,
            String aKeyName, String aKeyValue, String aPseudo )
        {
        Document document = aParent.getOwnerDocument();

        String namespaceUri = aParent.getNamespaceURI();

        Element newElement = document.createElementNS( namespaceUri,
                aElementName );

        if ( aPseudo != null )
            {
            newElement.setAttribute( STRING_PSEUDOCLASS, aPseudo );
            }
        newElement.setAttribute( STRING_NAME, aKeyName );
        newElement.setAttribute( STRING_VALUE, aKeyValue );

        aParent.appendChild( newElement );
        return newElement;
        }


    /**
     * Class for temporarily store Node's attribute name and value.
     */
    private class NameValuePair
        {
        private String iName;

        private String iValue;

        NameValuePair( String aName, String aValue )
            {
            iName = aName;
            iValue = aValue;
            }

        public String getName()
            {
            return iName;
            }

        public String getValue()
            {
            return iValue;
            }

        }

    }
