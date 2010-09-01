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
 * Description:  Uses XML parser to read the manifest and created objects that
 *                represent the manifest.
 *
 */

package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import com.nokia.tools.themeinstaller.localisation.DTDReader;
import com.nokia.tools.themeinstaller.localisation.Localisation;
import com.nokia.tools.themeinstaller.localisation.LocalisationStore;
import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.odtconverter.MimeTypeResolver;
import com.nokia.tools.themeinstaller.odtconverter.ThemeStatusResolver;
import com.nokia.tools.themeinstaller.xmlparser.XMLParser;

/**
 * Uses XML parser to read the manifest and created objects that represent the
 * manifest.
 */
public class ManifestFactory implements IParseOperationListener {

	// CONSTANTS
	// Manifest root node names
	private static final String MULTI_THEME = "datfiles";

	// Manifest element names
	private static final String APP_UID_ELEMENT = "AppUid";
	private static final String PROVIDER_UID_ELEMENT = "Provideruid";
	private static final String THEME_UID_ELEMENT = "ThemeUid";
	private static final String THEME_STATUS_ELEMENT = "ThemeStatus";
	private static final String THEME_FULL_NAME_ELEMENT = "ThemeFullName";
	private static final String THEME_SHORT_NAME_ELEMENT = "ThemeShortName";
	private static final String THEME_VERSION_ELEMENT = "ThemeVersion";
	private static final String FILE_XML_ELEMENT = "FileXML";
	private static final String FILE_CSS_ELEMENT = "FileCSS";
	private static final String FILE_DTD_ELEMENT = "FileDTD";
	private static final String FILE_DAT_ELEMENT = "FileDAT";
	private static final String FILE_RESOURCE_ELEMENT = "FileResource";
	private static final String CACHE_VALUE_MEMORY = "CacheMemory";
	private static final String LOCKING_ELEMENT = "Locking";
	private static final String LOCKED_VALUE = "Locked";
	private static final String CACHE_TYPE_ELEMENT = "CacheType";
	private static final String CACHE_VALUE_NONE = "CacheNone";
	private static final String CACHE_VALUE_FILE = "CacheFile";

	// Language element names
	private static final String LANGUAGE_SPECIFIC_ELEMENT = "LanguageSpecific";
	private static final int LANGUAGE_INDEPENDENT = 0;
	private static final int LANG_NOT_SET = -1;

	// Integer conversion radix
	private static final int RADIX = 16;

	// Screen size
	private static final int SCREEN_SIZE_X = 0;
	private static final int SCREEN_SIZE_Y = 0;

	// Resource file cache type
	public static int CACHE_TYPE_CACHE_NONE = 0;
	public static int CACHE_TYPE_CACHE_FILE = 1;
	public static int CACHE_TYPE_CACHE_MEMORY = 2;

	// Locking policy flag-definition from native, bit-masked.
	public static final int E_XN_UNLOCKED = 0x0000; // 0b0000000000000000,
	public static final int E_XN_LOCKED = 0x0001; // 0b0000000000000001,

	public static final String CURRENT_DIR = ".";

	// Property keys
	private static final String THEME_PROVIDER_KEY = "theme_provider_name";
	private static final String NAME_SPACE_KEY = "theme_name_space";

	// Lock for monitoring parse operation completions
	private Lock iLock;

	// Mime type resolver
	private MimeTypeResolver iMimeTypeResolver;

	// Converter properties
	private ConverterProperties iProperties;

	// Localisation settings
	private File iLocSettings;

	/**
	 * Constructor.
	 * 
	 * @param aLocSettings
	 *            Localisation settings
	 * @throws IOException
	 *             if converter properties can not be read
	 */
	public ManifestFactory(File aLocSettings) throws IOException {
		iLock = new Lock();
		iMimeTypeResolver = new MimeTypeResolver();
		iProperties = ConverterProperties.getInstance();
		iLocSettings = aLocSettings;
	}

	/**
	 * Parse a manifest and create the manifest object.
	 * 
	 * @param aFile
	 *            Manifest file
	 * @return Manifest instance
	 * @throws IOException
	 *             if the manifest can not be read
	 */
	public IThemeManifest createManifest(File aFile) throws IOException {
		// Read the manifest to the DOM document
		Document document = readManifest(aFile);
		IThemeManifest manifest = new ThemeManifest();

		// Set data directory that contains the data files of the theme
		if (aFile.getParent() == null) {
			manifest.setDataDir(CURRENT_DIR + File.separatorChar);
		} else {
			manifest.setDataDir(aFile.getParent() + File.separatorChar);
		}

		// Parse manifest contents
		String rootNodeName = document.getFirstChild().getNodeName();
		if (rootNodeName == MULTI_THEME) {
			// Multi theme manifest
			parseMultiThemeManifest(document, manifest);
		} else {
			// Single theme manifest
			parseManifest(document, manifest);
			parseLanguageSpecificData(document, manifest);
			parseResources(document, manifest, LANGUAGE_INDEPENDENT);
		}

		return manifest;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seecom.nokia.tools.themeinstaller.odtconverter.IParseOperationListener#
	 * parseOperationCompleted(int, java.lang.String)
	 */
	public void parseOperationCompleted(int aErr, String aReason) {
		iLock.unLock();
		if (aErr != 0) {
			throw new IllegalArgumentException(
					"Theme manifest parsing failed: " + aErr + ", " + aReason);
		}
	}

	/**
	 * Parse the manifest file.
	 * 
	 * @param aManifest
	 *            Manifest file
	 * @return DOM Document of the manifest
	 */
	private Document readManifest(File aManifest) {
		// Parse the manifest
		XMLParser parser = new XMLParser(aManifest.getPath());
		parser.addListener(this);

		try {
			parser.parse();
		} catch (Exception e) {
			throw new IllegalArgumentException(
					"Theme manifest parsing failed: " + e.getMessage());
		}

		// Wait for the operation completion
		iLock.lock();

		// Return the document that was formed
		return parser.getDOMDocument();
	}

	/**
	 * Parses a multi theme manifest from DOM to the manifest instance.
	 * 
	 * @param aDocument
	 *            DOM Document containing the manifest data (source)
	 * @param aManifest
	 *            Theme manifest (destination)
	 */
	private void parseMultiThemeManifest(Document aDocument,
			IThemeManifest aManifest) {
		// Add DAT file names
		NodeList nodes = aDocument.getElementsByTagName(FILE_DAT_ELEMENT);
		Node node = null;
		for (int i = 0; i < nodes.getLength(); i++) {
			node = nodes.item(i);
			aManifest.addManifestFile(aManifest.getDataDir()
					+ node.getTextContent());
		}
	}

	/**
	 * Parses a manifest from DOM to the manifest instance.
	 * 
	 * @param aDocument
	 *            DOM Document containing the manifest data (source)
	 * @param aManifest
	 *            Theme manifest (destination)
	 */
	private void parseManifest(Document aDocument, IThemeManifest aManifest) {
		// Set application uid
		NodeList nodes = aDocument.getElementsByTagName(APP_UID_ELEMENT);
		Node node = checkOneNode(nodes, APP_UID_ELEMENT);
		if (node != null)
			aManifest.setApplicationUid(Long.valueOf(node.getTextContent(),
					RADIX));

		// Set provider uid
		nodes = aDocument.getElementsByTagName(PROVIDER_UID_ELEMENT);
		node = checkOneNode(nodes, PROVIDER_UID_ELEMENT);
		if (node != null)
			aManifest
					.setProviderUid(Long.valueOf(node.getTextContent(), RADIX));

		// Set theme uid
		nodes = aDocument.getElementsByTagName(THEME_UID_ELEMENT);
		node = checkOneNode(nodes, THEME_UID_ELEMENT);
		if (node != null)
			aManifest.setThemeUid(Long.valueOf(node.getTextContent(), RADIX));

		// Set name space
		aManifest.setNameSpace(iProperties.getProperty(NAME_SPACE_KEY));

		// Set theme provider name
		aManifest.setProviderName(iProperties.getProperty(THEME_PROVIDER_KEY));

		// Set default theme full name before localization
		nodes = aDocument.getElementsByTagName(THEME_FULL_NAME_ELEMENT);
		if (nodes.getLength() > 0) {
			// Get first theme name that is found (for a default name).
			// The used name is specified in the language specific data.
			aManifest.setThemeFullName(nodes.item(0).getTextContent());
		}
		// else
		// {
		// throw new IllegalArgumentException(
		// "Syntax error in manifest file: theme full name not found" );
		// }

		// Set theme short name
		nodes = aDocument.getElementsByTagName(THEME_SHORT_NAME_ELEMENT);
		node = checkOneNode(nodes, THEME_SHORT_NAME_ELEMENT);
		if (node != null)
			aManifest.setThemeShortName(node.getTextContent());

		// Set theme version
		nodes = aDocument.getElementsByTagName(THEME_VERSION_ELEMENT);
		node = checkOneNode(nodes, THEME_VERSION_ELEMENT);
		if (node != null)
			aManifest.setThemeVersion(node.getTextContent());

		// Screen size, not used in Xuikon at the moment
		aManifest.setScreenSizeX(new Integer(SCREEN_SIZE_X));
		aManifest.setScreenSizeY(new Integer(SCREEN_SIZE_Y));

		// Resolve theme status
		nodes = aDocument.getElementsByTagName(THEME_STATUS_ELEMENT);
		int flags = ThemeStatusResolver.E_XN_THEME_STATUS_NONE;
		for (int i = 0; i < nodes.getLength(); i++) {
			node = nodes.item(i);
			flags |= ThemeStatusResolver.getValue(node.getTextContent())
					.intValue();
			if (node.getTextContent().equals(
					ThemeStatusResolver.THEME_STATUS_LICENCEE_RESTORABLE)) {
				// This theme is restored when licensee default theme is
				// restored.
				// When using this flag, the ThemeStatusLicenceeDefault-flag
				// must be activated.
				flags |= ThemeStatusResolver.E_XN_THEME_STATUS_LICENCEE_DEFAULT;
			}
		}
		aManifest.setThemeStatus(new Integer(flags));

		// Set XML file name
		NodeList files = aDocument.getElementsByTagName(FILE_XML_ELEMENT);
		node = checkOneNode(files, FILE_XML_ELEMENT);
		if (node != null)
			aManifest.setXMLFile(node.getTextContent());

		// Set CSS file name
		files = aDocument.getElementsByTagName(FILE_CSS_ELEMENT);
		node = checkMaxOneLanguageIndependentNode(files);
		if (node != null) {
			aManifest.setCSSFile(node.getTextContent());
		}

		// Set DTD file name
		files = aDocument.getElementsByTagName(FILE_DTD_ELEMENT);
		node = checkMaxOneLanguageIndependentNode(files);
		if (node != null) {
			aManifest.setDTDFile(node.getTextContent());
		}
	}

	/**
	 * Parses language specific data in the manifest.
	 * 
	 * @param aDocument
	 *            DOM Document containing the manifest data (source)
	 * @param aManifest
	 *            Theme manifest (destination)
	 * @throws IOException
	 *             if the manifest can not be parsed
	 */
	private void parseLanguageSpecificData(Document aDocument,
			IThemeManifest aManifest) throws IOException {
		// Get languages
		NodeList languages = aDocument
				.getElementsByTagName(LANGUAGE_SPECIFIC_ELEMENT);

		Node langSpecificNode = null;
		NamedNodeMap langAttr = null;
		NodeList langSpecificChildren = null;
		Node langSpecificChild = null;

		NodeList resources = aDocument
				.getElementsByTagName(FILE_RESOURCE_ELEMENT);
		Vector langResources = null;

		// Process all languages
		for (int i = 0; i < languages.getLength(); i++) {
			// Language specific data
			int langId = LANG_NOT_SET;
			String extDtd = null;
			String extCss = null;
			String themeFullName = null;

			// Take a LanguageSpecific node
			langSpecificNode = languages.item(i);

			// There should be only one language for each LanguageSpecific node
			langAttr = langSpecificNode.getAttributes();
			if (langAttr.getLength() == 1) {
				String langStr = langAttr.item(0).getNodeValue();
				langId = Integer.valueOf(langStr).intValue();
			}

			langSpecificChildren = langSpecificNode.getChildNodes();

			// Read language specific elements
			String nodeName = null;

			for (int j = 0; j < langSpecificChildren.getLength(); j++) {
				langSpecificChild = langSpecificChildren.item(j);
				nodeName = langSpecificChild.getNodeName();

				// Language specific DTD file name
				if (FILE_DTD_ELEMENT.equals(nodeName)) {
					extDtd = langSpecificChild.getTextContent();
				}
				// Language specific CSS
				else if (FILE_CSS_ELEMENT.equals(nodeName)) {
					extCss = langSpecificChild.getTextContent();
				}
				// Localized theme full name
				else if (THEME_FULL_NAME_ELEMENT.equals(nodeName)) {
					themeFullName = langSpecificChild.getTextContent();
				}
			}

			// Parse language specific resources
			langResources = parseResources(aManifest, resources, langId);

			// Verify that mandatory fields language id and DTD file were set
			if (langId == LANG_NOT_SET || extDtd == null) {
				throw new IllegalArgumentException(
						"Syntax error in language specifications of the manifest");
			}

			// Find the DTD file for reading the localised theme full name
			File dtd = null;
			if (iLocSettings != null) {
				// Use enhanced localisation: Find the DTD file
				LocalisationStore ls = LocalisationStore
						.getInstance(iLocSettings);
				Localisation l = ls.getLocalisation(aManifest
						.getApplicationUid().longValue(), aManifest
						.getProviderUid().longValue(), aManifest.getThemeUid()
						.longValue());
				dtd = l.findDTD(extDtd);
			} else {
				dtd = new File(aManifest.getDataDir() + extDtd);
			}

			// Resolve localised theme full name, if specified
			themeFullName = DTDReader.readEntity(dtd, themeFullName);

			// Create new language specific data and add it to the languages
			// list
			LanguageSpecificData language = new LanguageSpecificData(
					new Integer(langId), extDtd, extCss, themeFullName,
					langResources);
			aManifest.addLanguage(language);
		}

		// Unlocalized variant (causes the .o0000 file to be generated)
		LanguageSpecificData language = new LanguageSpecificData(new Integer(
				LANGUAGE_INDEPENDENT), null, null, null, null);
		aManifest.addLanguage(language);
	}

	/**
	 * Parses resource data in the manifest.
	 * 
	 * @param aDocument
	 *            DOM Document containing the manifest data (source)
	 * @param aManifest
	 *            Theme manifest (destination)
	 * @param aLanguageId
	 *            Id of the language of which resources will be parsed. On 0,
	 *            only language independent resources are parsed.
	 */
	private void parseResources(Document aDocument, IThemeManifest aManifest,
			int aLanguageId) {
		// Do the parsing operation
		NodeList resourceList = aDocument
				.getElementsByTagName(FILE_RESOURCE_ELEMENT);
		Vector resources = parseResources(aManifest, resourceList, aLanguageId);

		// Add resources to the manifest
		Enumeration e = resources.elements();
		while (e.hasMoreElements()) {
			aManifest.addResource((ThemeResource) e.nextElement());
		}
	}

	/**
	 * Parses resource files defined in the manifest. Resources must be parsed
	 * after the rest of the manifest is parsed. Theme status is used here for
	 * determining locking policies.
	 * 
	 * @param aManifest
	 *            Theme manifest
	 * @param aNodeList
	 *            Node list to parse
	 * @param aLanguageId
	 *            Id of the language of which resources will be parsed. On 0,
	 *            only language independent resources are parsed.
	 */
	private Vector parseResources(IThemeManifest aManifest, NodeList aNodeList,
			int aLanguageId) {
		Vector result = new Vector();
		Node node = null;

		// Browse through all resources in the list
		int count = aNodeList.getLength();
		for (int i = 0; i < count; i++) {
			node = aNodeList.item(i);
			String filename = node.getTextContent();
			NamedNodeMap attributes = node.getAttributes();

			int cacheType = CACHE_TYPE_CACHE_NONE;
			int lockingPolicy = E_XN_UNLOCKED;

			// Set cache type
			Node cacheTypeNode = attributes.getNamedItem(CACHE_TYPE_ELEMENT);
			if ((cacheTypeNode == null)
					|| cacheTypeNode.getTextContent().equals(CACHE_VALUE_NONE)) {
				cacheType = CACHE_TYPE_CACHE_NONE;
			} else if (cacheTypeNode.getTextContent().equals(CACHE_VALUE_FILE)) {
				cacheType = CACHE_TYPE_CACHE_FILE;
			} else if (cacheTypeNode.getTextContent()
					.equals(CACHE_VALUE_MEMORY)) {
				cacheType = CACHE_TYPE_CACHE_MEMORY;
			} else {
				throw new IllegalArgumentException(
						"Syntax error in the manifest, can not resolve resource cache type");
			}

			// Set locking policy
			Node locking = attributes.getNamedItem(LOCKING_ELEMENT);
			if (locking != null
					&& locking.getTextContent().equals(LOCKED_VALUE)) {
				lockingPolicy = E_XN_LOCKED;
			}

			// If EXnThemeStatusLicenceeDefault flag is set, locking policy is
			// E_XN_LOCKED
			if ((aManifest.getThemeStatus().intValue() & ThemeStatusResolver.E_XN_THEME_STATUS_LICENCEE_DEFAULT) != 0) {
				lockingPolicy = E_XN_LOCKED;
			}

			// Resolve mime type
			String mime = iMimeTypeResolver.getMimeType(filename);

			// Resolve resource type
			int resourceType = iMimeTypeResolver.getResourceType(filename);

			// Verify language id
			Node parent = node.getParentNode();
			NamedNodeMap attr = parent.getAttributes();

			// Language specific resources
			if (attr.getLength() == 1
					&& aLanguageId == Integer.valueOf(
							attr.item(0).getNodeValue()).intValue()) {
				ThemeResource resource = new ThemeResource(filename, cacheType,
						lockingPolicy, aManifest.getNameSpace(), resourceType,
						mime);
				result.add(resource);
			}
			// Language independent resources
			else if (aLanguageId == LANGUAGE_INDEPENDENT
					&& !LANGUAGE_SPECIFIC_ELEMENT.equals(parent.getNodeName())) {
				ThemeResource resource = new ThemeResource(filename, cacheType,
						lockingPolicy, aManifest.getNameSpace(), resourceType,
						mime);
				result.add(resource);
			}
		}

		return result;
	}

	/**
	 * Checks that there exists just one node in the list
	 * 
	 * @param aNodeList
	 *            Node list to be checked
	 * @return Only one existing node
	 * @throws IllegalArgumentException
	 *             If there is more or less than one node in list
	 */
	private Node checkOneNode(NodeList aNodeList, String tagName) {

		if (aNodeList.getLength() > 1) {
			 throw new IllegalArgumentException(
			 "Syntax error in manifest file, more child nodes than expected");
		}
		return aNodeList.item(0);
	}

	/**
	 * Checks that there exists max one node in the list and it is language
	 * independent.
	 * 
	 * @param aNodeList
	 *            Node list to be checked
	 * @return The existing language independent node or null
	 * @throws IllegalArgumentException
	 *             If there is more or less than one node in list
	 */
	private Node checkMaxOneLanguageIndependentNode(NodeList aNodeList) {
		Node result = null;
		int count = 0;
		for (int i = 0; i < aNodeList.getLength(); i++) {
			// Verify language in-dependency
			Node node = aNodeList.item(i);
			Node parent = node.getParentNode();
			if (!LANGUAGE_SPECIFIC_ELEMENT.equals(parent.getNodeName())) {
				result = node;
				count++;
			}
		}

		if (count > 1) {
			throw new IllegalArgumentException(
					"Syntax error in manifest file, more language "
							+ "independent child nodes than expected");
		}

		return result;
	}

}
