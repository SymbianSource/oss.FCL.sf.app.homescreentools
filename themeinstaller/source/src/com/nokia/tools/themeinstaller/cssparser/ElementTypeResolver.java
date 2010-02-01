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
* Description:  ElementTypeResolver for Different element types
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.util.Hashtable;

/**
 * Resolves different element types by element name.
 *
 * Constants copied from Symbian side files:
 *   ..\EComElement\XnDomVisitor\src\xndomvisitor.cpp
 * and
 *   ..\EComElement\XnDomVisitor\inc\xnliteral.h
 *
 */
public class ElementTypeResolver
    {
    public static final String STRING_NONE                  = "none";
    public static final String STRING_UNSPECIFIED           = "unspecified";
    public static final String KProperty                    = "property";

    //Ui
    public static final String KXmluiml                     = "xmluiml";
    public static final String KInclude                     = "include";
    public static final String KViews                       = "views";
    public static final String KView                        = "view";
    public static final String KPanes                       = "panes";
    public static final String KStatusPane                  = "statuspane";
    public static final String KMainPane                    = "mainpane";
    public static final String KControlPane                 = "controlpane";
    public static final String KDialogs                     = "dialogs";
    public static final String KDialog                      = "dialog";
    public static final String KNote                        = "note";

    //Header
    public static final String KUiDefinition                = "uidefinition";
    public static final String KApplication                 = "application";
    public static final String KDesc                        = "desc";

    //Control
    public static final String KButton                      = "button";
    public static final String KGrid                        = "grid";
    public static final String KListItem                    = "listitem";
    public static final String KDataGrid                    = "datagrid";
    public static final String KGridCellTemplate            = "gridcelltemplate";
    public static final String KList                        = "list";
    public static final String KDataList                    = "datalist";
    public static final String KListRowTemplate             = "listrowtemplate";
    public static final String KMenuBar                     = "menubar";
    public static final String KMenu                        = "menu";
    public static final String KMenuItem                    = "menuitem";
    public static final String KText                        = "text";
    public static final String KImage                       = "image";
    public static final String KEditor                      = "editor";
    public static final String KMarquee                     = "marquee";
    public static final String KNewsticker                  = "newsticker";
    public static final String KTooltip                     = "tooltip";

    //XHTML
    public static final String KObject                      = "object";
    public static final String KParam                       = "param";

    //Box
    public static final String KBox                         = "box";

    //Interaction
    public static final String KAction                      = "action";
    public static final String KTrigger                     = "trigger";
    public static final String KEvent                       = "event";

    public static final String VIEW_ELEMENT                 = "viewElement";
    public static final String COMMON_ELEMENT               = "commonElement";
    public static final String TEXT_ELEMENT                 = "textElement";
    public static final String GRID_AND_DATAGRID_ELEMENT    = "gridAndDataGridelement";
    public static final String GRID_AND_LIST_ELEMENT        = "gridAndListElement";

    private Hashtable iElementTypeTable;

    /**
     * Instantiates a new element type resolver.
     */
    public ElementTypeResolver()
        {
        iElementTypeTable = new Hashtable();
        iElementTypeTable.put( KXmluiml,           STRING_UNSPECIFIED           );
        iElementTypeTable.put( KProperty,          STRING_UNSPECIFIED           );
        iElementTypeTable.put( KXmluiml,           STRING_UNSPECIFIED           );
        iElementTypeTable.put( KInclude,           STRING_UNSPECIFIED           );
        iElementTypeTable.put( KViews,             STRING_UNSPECIFIED           );
        iElementTypeTable.put( KView,              VIEW_ELEMENT                 );
        iElementTypeTable.put( KPanes,             COMMON_ELEMENT               );
        iElementTypeTable.put( KStatusPane,        COMMON_ELEMENT               );
        iElementTypeTable.put( KMainPane,          COMMON_ELEMENT               );
        iElementTypeTable.put( KControlPane,       COMMON_ELEMENT               );
        iElementTypeTable.put( KDialogs,           COMMON_ELEMENT               );
        iElementTypeTable.put( KDialog,            COMMON_ELEMENT               );
        iElementTypeTable.put( KNote,              TEXT_ELEMENT                 );
        iElementTypeTable.put( KUiDefinition,      STRING_UNSPECIFIED           );
        iElementTypeTable.put( KApplication,       STRING_UNSPECIFIED           );
        iElementTypeTable.put( KDesc,              STRING_UNSPECIFIED           );
        iElementTypeTable.put( KButton,            TEXT_ELEMENT                 );
        iElementTypeTable.put( KGrid,              GRID_AND_DATAGRID_ELEMENT    );
        iElementTypeTable.put( KListItem,          TEXT_ELEMENT                 );
        iElementTypeTable.put( KDataGrid,          GRID_AND_DATAGRID_ELEMENT    );
        iElementTypeTable.put( KGridCellTemplate,  COMMON_ELEMENT               );
        iElementTypeTable.put( KList,              GRID_AND_LIST_ELEMENT        );
        iElementTypeTable.put( KDataList,          GRID_AND_LIST_ELEMENT        );
        iElementTypeTable.put( KListRowTemplate,   COMMON_ELEMENT               );
        iElementTypeTable.put( KMenuBar,           STRING_UNSPECIFIED           );
        iElementTypeTable.put( KMenu,              STRING_UNSPECIFIED           );
        iElementTypeTable.put( KMenuItem,          STRING_UNSPECIFIED           );
        iElementTypeTable.put( KText,              TEXT_ELEMENT                 );
        iElementTypeTable.put( KImage,             COMMON_ELEMENT               );
        iElementTypeTable.put( KEditor,            TEXT_ELEMENT                 );
        iElementTypeTable.put( KMarquee,           TEXT_ELEMENT                 );
        iElementTypeTable.put( KNewsticker,        TEXT_ELEMENT                 );
        iElementTypeTable.put( KObject,            STRING_UNSPECIFIED           );
        iElementTypeTable.put( KParam,             STRING_UNSPECIFIED           );
        iElementTypeTable.put( KTooltip,           TEXT_ELEMENT                 );
        iElementTypeTable.put( KBox,               COMMON_ELEMENT               );
        iElementTypeTable.put( KAction,            STRING_UNSPECIFIED           );
        iElementTypeTable.put( KTrigger,           STRING_UNSPECIFIED           );
        iElementTypeTable.put( KEvent,             STRING_UNSPECIFIED           );
        }

    /**
     * Gets the elements type.
     *
     * @param aKey Elements name
     *
     * @return The elements type
     */
    public String getValue( String aKey )
        {
        if ( iElementTypeTable.containsKey( aKey ) )
            {
            return ( String ) iElementTypeTable.get( aKey );
            }
        return STRING_NONE;
        }

    /**
     * Resolves if element can have inherited properties.
     *
     * @param aKey Elements name
     *
     * @return true, Element with given name can inherit properties
     */
    public boolean canInherit( String aKey )
        {
        if ( !iElementTypeTable.containsKey( aKey ) )
            {
            return false;
            }
        if ( iElementTypeTable.get( aKey ).equals( STRING_UNSPECIFIED ) )
            {
            return false;
            }
        return true;
        }
    }
