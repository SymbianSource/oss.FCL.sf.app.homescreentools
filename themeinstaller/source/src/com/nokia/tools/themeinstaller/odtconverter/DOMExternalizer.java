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
* Description:  Externalizes a DOM Document to a byte array.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.awt.Color;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import com.nokia.tools.themeinstaller.cssparser.CSSDOMProcessor;
import com.nokia.tools.themeinstaller.cssparser.CSSHandler;
import com.nokia.tools.themeinstaller.cssparser.PseudoClassResolver;

/**
 * Externalizes DOM Document to a byte array.
 */
public class DOMExternalizer
    {

    // CONSTANTS
    // Text elements according to CXnDomVisitor::KXnElementVisitorTable and
    // CXnODTParser
    private static final String TEXT_ELEMENT = "text";
    private static final String DESC_ELEMENT = "desc";
    private static final String MARQUEE_ELEMENT = "marquee";
    private static final String OBJECT_ELEMENT = "object";
    private static final String NEWSTICKER_ELEMENT = "newsticker";

    // Attribute name if node is refnode
    private static final String REF_NODE = "ref";

    // List types
    private static final int UNKNOWN = -1;
    private static final int NODE = 0;
    private static final int ATTRIBUTE = 1;
    private static final int PROPERTY = 2;

    // The Constant COLOR_TABLE_SIZE
    private static final int COLOR_TABLE_SIZE = 3;

    // Pseudo class resolver
    private PseudoClassResolver iPseudoResolver;

    // The value type resolver
    private ValueTypeResolver iValueTypeResolver;

    // String pool
    private StringPool iStringPool;

    // DOM Document
    private Document iDocument;

    // Byte output stream for delivering the externalized data
    private ByteArrayOutputStream iBaos;

    // Data output stream for writing to the baos
    private ODTDataOutputStream iODTDos;

    // Node id and counter
    private int iCurrentNodeId = 0;

    /** CSSDOMProsessor for checking property's inheritance value. */
    private CSSDOMProcessor iCSSDOMProsessor;

    /**
     * Constructor.
     * @param aDocument DOM Document to externalize
     */
    public DOMExternalizer( Document aDocument )
        {
        iPseudoResolver = new PseudoClassResolver();
        iValueTypeResolver = new ValueTypeResolver();
        iCSSDOMProsessor = new CSSDOMProcessor();
        iStringPool = new StringPool();
        iDocument = aDocument;
        iBaos = new ByteArrayOutputStream();
        iODTDos = new ODTDataOutputStream( iBaos );
        }

    /* (non-Javadoc)
     * @see java.lang.Object#finalize()
     */
    protected void finalize() throws Throwable
        {
        iODTDos.close();
        iBaos.close();
        }

    /**
     * Externalizes the DOM document and string pool to a byte array.
     * @return Byte array containing the document
     * @throws IOException if writing to a stream fails
     * @throws ODTException
     */
    public byte[] getByteArray() throws IOException, ODTException
        {
        ByteArrayOutputStream result = new ByteArrayOutputStream();
        byte[] resultArray = null;

        try
            {
            // Externalize the DOM
            doExternalize();

            // Externalize the string pool
            result.write( iStringPool.toByteArray() );

            // Write the dom contents to the result baos
            result.write( iBaos.toByteArray() );

            resultArray = result.toByteArray();
            }
        finally
            {
            if( result != null )
                {
                result.close();
                }
            }

        return resultArray;
        }

    /**
     * Do the externalization process.
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with property value externalization
     */
    private void doExternalize() throws IOException, ODTException
        {
        Node rootElement = iDocument.getDocumentElement();

        if( rootElement != null )
            {
            // Root node exists
            iODTDos.writeBoolean( true );
            externalizeNode( ( Node )rootElement, true );
            }
        else
            {
            // No root node
            iODTDos.writeBoolean( false );
            }
        }

    /**
     * Externalizes a node in the DOM tree.
     * @param aNode Node to externalize
     * @param aRootNode true, if this is the root node of the tree
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with property value externalization
     */
    private void externalizeNode( Node aNode, boolean aRootNode )
        throws IOException, ODTException
        {
        // Write name
        String name = aNode.getNodeName();
        int nameRef = iStringPool.addString( name );
        iODTDos.writeInt16( nameRef );

        // Write name space
        String ns = aNode.getNamespaceURI();
        int nsRef = iStringPool.addString( ns );
        iODTDos.writeInt16( nsRef );

        // Check and write refnode boolean
        iODTDos.writeBoolean( checkRefNode( aNode ) );

        boolean textNodeFound = false;

        // Write parsed character data
        StringBuffer pcData = new StringBuffer();
        if( TEXT_ELEMENT.equals( name ) ||
            DESC_ELEMENT.equals( name ) ||
            MARQUEE_ELEMENT.equals( name ) ||
            OBJECT_ELEMENT.equals( name ) ||
            NEWSTICKER_ELEMENT.equals( name ) )
            {
            NodeList list = aNode.getChildNodes();

            for( int i = 0; i < list.getLength() ; i++ )
                {
                Node nod = list.item( i );
                if( nod.getNodeType() == Node.TEXT_NODE )
                    {
                    textNodeFound = true;
                    String textNodeValue = nod.getNodeValue();

                    pcData.append( textNodeValue );
                    }
                }
            }

        // Write data length and the data
        iODTDos.writeBoolean( textNodeFound );
        if( textNodeFound )
            {
            // Write text length
            iODTDos.writeInt16( pcData.length() );

            // Write text node value
            iODTDos.writeString8( pcData.toString() );
            }
        // Update the counter and write node id
        iODTDos.writeInt32( iCurrentNodeId++ );

        // Externalize the child list
        externalizeNodeList( aNode );

        // Externalize the attribute list
        externalizeAttributeList( aNode );

        // Externalize the property list
        externalizePropertyList( aNode );
        }

    /**
     * Checks if node is refnode.
     * Node is refnode if some of node's attributes name is "ref".
     * @param aNode Node containing the attributes
     * @return boolean true if node is refnode, otherwise false
     */
    private boolean checkRefNode( Node aNode )
        {
        boolean refNode = false;
        NamedNodeMap list = aNode.getAttributes();
        for ( int i = 0; i < list.getLength(); i++ )
            {
            Node node = list.item( i );
            if ( nodeType( node ) == ATTRIBUTE )
                {
                if( node.getNodeName().equals( REF_NODE ) )
                    {
                    refNode = true;
                    }
                }
            }
        return refNode;
        }

    /**
     * Externalizes attributes of a node.
     * @param aNode Node containing the attributes
     * @throws IOException if writing to a stream fails
     * @throws ODTException
     */
    private void externalizeAttributeNode( Node aNode )
        throws IOException, ODTException
        {
        // Write name
        String name = aNode.getNodeName();
        int nameRef = iStringPool.addString( name );
        iODTDos.writeInt16( nameRef );

        // Write value
        String value = aNode.getNodeValue();
        int valueRef = iStringPool.addString( value );
        iODTDos.writeInt16( valueRef );
        }

    /**
     * Externalizes a property node.
     *
     * @param aNode Node containing the properties
     * @param aParentNode Node's parent node
     *
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with property
     * value externalization
     */
    private void externalizePropertyNode( Node aParentNode, Node aNode )
        throws IOException, ODTException
        {
        // Get property node attributes: property name, values and pseudo class
        NamedNodeMap list = aNode.getAttributes();

        // Property value list
        boolean isInherited = externalizePropertyValueList( aParentNode, list );

        iODTDos.writeBoolean( isInherited );

        // Resolve pseudo class
        int pseudoClass = PseudoClassResolver.NONE;

        int count = list.getLength();
        for( int i = 0; i < count; i++ )
            {
            // Browse through all attributes of the style property element and
            // seek for a pseudo class
            Node item = list.item( i );
            if( item.getNodeName().equals( CSSDOMProcessor.STRING_PSEUDOCLASS ) )
                {
                pseudoClass = iPseudoResolver.getKey( item.getNodeValue() );
                if( pseudoClass == UNKNOWN )
                    {
                    throw new ODTException( "Error externalizing ODT/styles: " +
                    		"unknown pseudo class" );
                    }
                break;
                }
            }

        // Pseudo class -> int8
        iODTDos.writeByte( pseudoClass );
        }

    /**
     * Externalize a list of nodes.
     * @param aParentNode Parent node
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with property value externalization
     */
    private void externalizeNodeList( Node aParentNode ) throws IOException, ODTException
        {
        // Write list type
        iODTDos.writeByte( NODE );

        NodeList list = aParentNode.getChildNodes();

        // Count element nodes
        int count = countNodes( list );

        // Write element node count
        iODTDos.writeInt32( count );

        for ( int i = 0; i < list.getLength(); i++ )
            {
            Node node = list.item( i );

            if ( nodeType( node ) == NODE )
                {
                externalizeNode( node, false );
                }
            }
        }

    /**
     * Externalize a list of attributes.
     * @param aParentNode Node containing the attributes.
     * @throws IOException if writing to a stream fails
     * @throws ODTException
     */
    private void externalizeAttributeList( Node aParentNode )
            throws IOException, ODTException
        {
        // Write list type
        iODTDos.writeByte( ATTRIBUTE );

        NamedNodeMap list = aParentNode.getAttributes();

        // Count element nodes
        int count = countAttributes( list );

        // Write element node count
        iODTDos.writeInt32( count );

        for ( int i = 0; i < list.getLength(); i++ )
            {
            Node node = list.item( i );

            if ( nodeType( node ) == ATTRIBUTE )
                {
                externalizeAttributeNode( node );
                }
            }
        }

    /**
     * Externalize a list of properties.
     * @param aParentNode Node containing the properties
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with property value externalization
     */
    private void externalizePropertyList( Node aParentNode ) throws IOException, ODTException
        {
        // Write list type
        iODTDos.writeByte( PROPERTY );

        NodeList list = aParentNode.getChildNodes();

        // Count element nodes
        int count = countProperties( list );

        // Write element node count
        iODTDos.writeInt32( count );

        for ( int i = 0; i < list.getLength(); i++ )
            {
            Node node = list.item( i );

            if ( nodeType( node ) == PROPERTY )
                {
                externalizePropertyNode( aParentNode, node );
                }
            }
        }

    /**
     * Parses a Color from string.
     *
     * @param aColor Color values in String made by CSSHandler
     *
     * @return The color
     *
     * @throws ODTException the ODT exception
     */
    private Color parseColorFromString( String aColor ) throws ODTException
        {
        String sx[] = aColor.split( CSSHandler.COMMA );
        int ix[] = new int[ sx.length ];

        // LexicalUnit.SAC_RGBCOLOR knows color values with format
        // rgb(0, 0, 0) and #000. That is, with three parameters
        if ( sx.length != COLOR_TABLE_SIZE )
            {
            throw new ODTException( "Error in DOM/style data externalization: "
                    + "RGB Values: parameter amount" );
            }

        for ( int i = 0; i < sx.length; i++ )
            {
            if ( sx[ i ].contains( CSSHandler.SEPARATOR ) )
                {
                // Check if single color's value is integer
                Short valueType = iValueTypeResolver.getValue( Short
                        .valueOf( sx[ i ].substring( 0, sx[ i ]
                                .indexOf( CSSHandler.SEPARATOR ) ) ) );

                if ( valueType.intValue() != ValueTypeResolver.E_NUMBER )
                    {
                    throw new ODTException(
                            "Error in DOM/style data externalization: "
                                    + "RGB Values: R, G or B not interger" );
                    }
                String redGreenBlue = sx[ i ].substring( sx[ i ]
                        .indexOf( CSSHandler.SEPARATOR ) + 1, sx[ i ]
                        .length() );
                Integer rgbValue = Integer.valueOf( redGreenBlue );
                ix[ i ] = rgbValue.intValue();
                }
            else
                {
                throw new ODTException(
                        "Error in DOM/style data externalization: "
                                + "RGB Values: can't resolve value type" );
                }
            }
        return new Color( ix[ 0 ], ix[ 1 ], ix[ 2 ] );
        }

    /**
     * Parses the Value Type from Value.
     *
     * @param aAttrValue The attribute value
     *
     * @return Parsed value as a string
     *
     * @throws IOException Signals that an I/O exception has occurred.
     * @throws ODTException
     */
    private String parseAttrValue( String aAttrValue, PropertyValue aPropValue )
        throws IOException, ODTException
        {
        if ( aAttrValue.length() > 0 )
            {
            if ( aAttrValue.contains( "|" ) )
                {
                String type = aAttrValue
                        .substring( 0, aAttrValue.indexOf( '|' ) );
                String value = aAttrValue.substring(
                        aAttrValue.indexOf( '|' ) + 1, aAttrValue.length() );

                Short lexicalUnit = Short.valueOf( type );
                Short primitiveValueType =
                        iValueTypeResolver.getValue( lexicalUnit );

                switch ( primitiveValueType.intValue() )
                    {
                    case ValueTypeResolver.E_NUMBER:
                        double doubleValueInteger = Double.valueOf( value ).doubleValue();
                        aPropValue.setRealValue( doubleValueInteger,
                                                 primitiveValueType.shortValue() );
                        break;
                    case ValueTypeResolver.E_UNIT_VALUE:
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
                        double doubleValuePercentage = Double.valueOf( value ).doubleValue();
                        aPropValue.setRealValue( doubleValuePercentage,
                                                 primitiveValueType.shortValue() );
                        break;
                    case ValueTypeResolver.E_IDENT:
                    case ValueTypeResolver.E_STRING:
                    case ValueTypeResolver.E_URI:
                    case ValueTypeResolver.E_ATTR:
                        aPropValue.setString( new String( value ),
                                primitiveValueType.shortValue() );
                        break;
                    case ValueTypeResolver.E_RGB_COLOR:
                        Color color = parseColorFromString(value);
                        aPropValue.setRgbValue( color );
                        break;
                    default:
                        break;
                    }

                return value;
                }
            return aAttrValue;
            }
        return aAttrValue;
        }

    /**
     * Externalize a list of property values.
     *
     * @param aNode the a node
     * @param aAttrList the a attr list
     *
     * @return true, if property is inherited
     *
     * @throws IOException if data output stream can not be written
     * @throws ODTException if there is an error with externalizing property values
     */
    private boolean externalizePropertyValueList( Node aNode, NamedNodeMap aAttrList )
        throws IOException, ODTException
        {
        PropertyValueList valueList = new PropertyValueList( iStringPool );

        boolean isInherited = false;
        String name = null;
        String value = null;

        for ( int i = 0; i < aAttrList.getLength(); i++ )
            {
            Node node = aAttrList.item( i );

            if ( nodeType( node ) == ATTRIBUTE &&
                 !node.getNodeName().equals( CSSDOMProcessor.STRING_PSEUDOCLASS ) )
                {
                String attrName = node.getNodeName();
                String attrValue = node.getNodeValue();

                if( attrName.equals( CSSDOMProcessor.STRING_NAME ) &&
                    name == null )
                    {
                    name = attrValue;
                    }
                    else if( attrName.startsWith( CSSDOMProcessor.STRING_VALUE ) )
                    {
                    value = attrValue;

                    // Checking if property is inherited.
                    // This emulates the behavior of the Symbian side implementation
                    // where this is true in following cases:
                    // 1. Value equals "inherited"
                    // 2. Property is inheritable and the element can inherit properties
                    //
                    // This means that also some properties that aren't actually
                    // inherited, are also set with value isIherited == "true"
                    isInherited = iCSSDOMProsessor.canInherit( (Element) aNode, name, value );

                    PropertyValue propValue = valueList.newItem();
                    parseAttrValue( value, propValue );
                    }
                else
                    {
                    throw new ODTException( "Error in DOM/style data externalization: " +
                    		"Property values" );
                    }
                }
            }

        if( name != null &&
            value != null )
            {
            // Write property name
            int nameRef = iStringPool.addString( name );
            iODTDos.writeInt16( nameRef );

            // Externalize the property value list to the stream
            valueList.externalize( iODTDos );
            }
        else
            {
            throw new ODTException( "Error in DOM/style data externalization: " +
            		"Property values" );
            }
        return isInherited;
        }

    /**
     * Count element nodes in a node list.
     * @param aList Node list
     * @param aNodeType Node type to count
     * @return Count of found nodes
     */
    private static int countNodes( NodeList aList )
        {
        int count = 0;
        for( int i = 0; i < aList.getLength(); i++ )
            {
            // Exclude elements that are style properties
            if( nodeType( aList.item( i ) ) == NODE )
                {
                count++;
                }
            }

        return count;
        }

    /**
     * Count attributes in a named node map.
     * @param aList Node map
     * @param aNodeType Node type to count
     * @return Count of found nodes
     */
    private static int countAttributes( NamedNodeMap aList )
        {
        int count = 0;
        for( int i = 0; i < aList.getLength(); i++ )
            {
            if( nodeType( aList.item( i ) ) == ATTRIBUTE )
                {
                count++;
                }
            }

        return count;
        }

    /**
     * Count properties in a node list.
     * @param aList Node list
     * @param aNodeType Node type to count
     * @return Count of found nodes
     */
    private static int countProperties( NodeList aList )
        {
        int count = 0;
        for( int i = 0; i < aList.getLength(); i++ )
            {
            // Include only elements that are style properties
            if( nodeType( aList.item( i ) ) == PROPERTY )
                {
                count++;
                }
            }

        return count;
        }

    /**
     * Resolve node type. Possible types: NODE, ATTRIBUTE or PROPERTY
     * @param aItem Node to resolve
     * @return Type of the node. If the type can not be determined, UNKNOWN is returned
     */
    private static int nodeType( Node aItem )
        {
        int type = UNKNOWN;

        // Element that is not a style property element
        if( aItem.getNodeType() == Node.ELEMENT_NODE &&
            !aItem.getNodeName().equals( CSSDOMProcessor.STRING_PROPERTY ) )
            {
            type = NODE;
            }
        // Attribute nodes
        else if( aItem.getNodeType() == Node.ATTRIBUTE_NODE )
            {
            type = ATTRIBUTE;
            }
        // Style property element
        else if( aItem.getNodeType() == Node.ELEMENT_NODE &&
                 aItem.getNodeName().equals( CSSDOMProcessor.STRING_PROPERTY ) )
            {
            type = PROPERTY;
            }

        return type;
        }

    }
