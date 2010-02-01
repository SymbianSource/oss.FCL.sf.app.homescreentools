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
* Description:  Color resolver for resolving colors set as strings.
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.awt.Color;
import java.util.Hashtable;

/**
 * Color resolver for resolving colors set as strings. Corresponding
 * functionality is implemented in Xuikon CSS Parser (cssconstants.h and
 * CCSSLexicalUnit).
 *
 * Color resolver also includes HSL to RGB converting.
 *
 */
public class ColorResolver extends Hashtable
    {

    // Default serial version UID
    private static final long serialVersionUID = 1L;
    private static final int RGB_MAX_VALUE = 255;
    private static final int PERCENTAGE_MAX_VALUE = 100;

    public ColorResolver()
        {
        // HTML4 color keywords
        put( "maroon", new Color( 128, 0, 0 ) );
        put( "red", new Color( 255, 0, 0 ) );
        put( "orange", new Color( 255, 165, 0 ) );
        put( "yellow", new Color( 255, 255, 0 ) );
        put( "olive", new Color( 128, 128, 0 ) );
        put( "purple", new Color( 128, 0, 128 ) );
        put( "fuchsia", new Color( 255, 0, 255 ) );
        put( "white", new Color( 255, 255, 255 ) );
        put( "lime", new Color( 0, 255, 0 ) );
        put( "green", new Color( 0, 128, 0 ) );
        put( "navy", new Color( 0, 0, 128 ) );
        put( "blue", new Color( 0, 0, 255 ) );
        put( "aqua", new Color( 0, 255, 255 ) );
        put( "teal", new Color( 0, 128, 128 ) );
        put( "black", new Color( 0, 0, 0 ) );
        put( "silver", new Color( 192, 192, 192 ) );
        put( "gray", new Color( 128, 128, 128 ) );

        // Transparent
        put( "transparent", new Color( 0, 0, 0, 0 ) );

        // SVG 1.0 COLOR KEYWORDS
        // (excl. the ones defined in the HTML4 colors set)
        put( "aliceblue", new Color( 240, 248, 255 ) );
        put( "antiquewhite", new Color( 250, 235, 215 ) );
        put( "aquamarine", new Color( 127, 255, 212 ) );
        put( "azure", new Color( 240, 255, 255 ) );
        put( "beige", new Color( 245, 245, 220 ) );
        put( "bisque", new Color( 255, 228, 196 ) );
        put( "blanchedalmond", new Color( 255, 235, 205 ) );
        put( "blueviolet", new Color( 138, 43, 226 ) );
        put( "brown", new Color( 165, 42, 42 ) );
        put( "burlywood", new Color( 222, 184, 135 ) );
        put( "cadetblue", new Color( 95, 158, 160 ) );
        put( "chartreuse", new Color( 127, 255, 0 ) );
        put( "chocolate", new Color( 210, 105, 30 ) );
        put( "coral", new Color( 255, 127, 80 ) );
        put( "cornflowerblue", new Color( 100, 149, 237 ) );
        put( "cornsilk", new Color( 255, 248, 220 ) );
        put( "crimson", new Color( 220, 20, 60 ) );
        put( "cyan", new Color( 0, 255, 255 ) );
        put( "darkblue", new Color( 0, 0, 139 ) );
        put( "darkcyan", new Color( 0, 139, 139 ) );
        put( "darkgoldenrod", new Color( 184, 134, 11 ) );
        put( "darkgray", new Color( 169, 169, 169 ) );
        put( "darkgrey", new Color( 169, 169, 169 ) );
        put( "darkgreen", new Color( 0, 100, 0 ) );
        put( "darkkhaki", new Color( 189, 183, 107 ) );
        put( "darkmagenta", new Color( 139, 0, 139 ) );
        put( "darkolivegreen", new Color( 85, 107, 47 ) );
        put( "darkorange", new Color( 255, 140, 0 ) );
        put( "darkorchid", new Color( 153, 50, 204 ) );
        put( "darkred", new Color( 139, 0, 0 ) );
        put( "darksalmon", new Color( 233, 150, 122 ) );
        put( "darkseagreen", new Color( 143, 188, 143 ) );
        put( "darkslateblue", new Color( 72, 61, 139 ) );
        put( "darkslategray", new Color( 47, 79, 79 ) );
        put( "darkslategrey", new Color( 47, 79, 79 ) );
        put( "darkturquoise", new Color( 0, 206, 209 ) );
        put( "darkviolet", new Color( 148, 0, 211 ) );
        put( "deeppink", new Color( 255, 20, 147 ) );
        put( "deepskyblue", new Color( 0, 191, 255 ) );
        put( "dimgray", new Color( 105, 105, 105 ) );
        put( "dimgrey", new Color( 105, 105, 105 ) );
        put( "dodgerblue", new Color( 30, 144, 255 ) );
        put( "firebrick", new Color( 178, 34, 34 ) );
        put( "floralwhite", new Color( 255, 250, 240 ) );
        put( "forestgreen", new Color( 34, 139, 34 ) );
        put( "fuchsia", new Color( 255, 0, 255 ) );
        put( "gainsboro", new Color( 220, 220, 220 ) );
        put( "ghostwhite", new Color( 248, 248, 255 ) );
        put( "gold", new Color( 255, 215, 0 ) );
        put( "goldenrod", new Color( 218, 165, 32 ) );
        put( "greenyellow", new Color( 173, 255, 47 ) );
        put( "grey", new Color( 240, 255, 240 ) );
        put( "honeydew", new Color( 240, 255, 240 ) );
        put( "hotpink", new Color( 255, 105, 180 ) );
        put( "indianred", new Color( 205, 92, 92 ) );
        put( "indigo", new Color( 75, 0, 130 ) );
        put( "ivory", new Color( 255, 255, 240 ) );
        put( "khaki", new Color( 240, 230, 140 ) );
        put( "lavender", new Color( 230, 230, 250 ) );
        put( "lavenderblush", new Color( 255, 240, 245 ) );
        put( "lawngreen", new Color( 124, 252, 0 ) );
        put( "lemonchiffon", new Color( 255, 250, 205 ) );
        put( "lightblue", new Color( 173, 216, 230 ) );
        put( "lightcoral", new Color( 240, 128, 128 ) );
        put( "lightcyan", new Color( 224, 255, 255 ) );
        put( "lightgoldenrodyellow", new Color( 250, 250, 210 ) );
        put( "lightgray", new Color( 211, 211, 211 ) );
        put( "lightgrey", new Color( 211, 211, 211 ) );
        put( "lightgreen", new Color( 144, 238, 144 ) );
        put( "lightpink", new Color( 255, 182, 193 ) );
        put( "lightsalmon", new Color( 255, 160, 122 ) );
        put( "lightseagreen", new Color( 32, 178, 170 ) );
        put( "lightskyblue", new Color( 135, 206, 250 ) );
        put( "lightslategray", new Color( 119, 136, 153 ) );
        put( "lightslategrey", new Color( 119, 136, 153 ) );
        put( "lightsteelblue", new Color( 176, 196, 222 ) );
        put( "lightyellow", new Color( 255, 255, 224 ) );
        put( "limegreen", new Color( 50, 205, 50 ) );
        put( "linen", new Color( 250, 240, 230 ) );
        put( "magenta", new Color( 255, 0, 255 ) );
        put( "mediumaquamarine", new Color( 102, 205, 170 ) );
        put( "mediumblue", new Color( 0, 0, 205 ) );
        put( "mediumorchid", new Color( 186, 85, 211 ) );
        put( "mediumpurple", new Color( 147, 112, 219 ) );
        put( "mediumseagreen", new Color( 60, 179, 113 ) );
        put( "mediumslateblue", new Color( 123, 104, 238 ) );
        put( "mediumspringgreen", new Color( 0, 250, 154 ) );
        put( "mediumturquoise", new Color( 72, 209, 204 ) );
        put( "mediumvioletred", new Color( 199, 21, 133 ) );
        put( "midnightblue", new Color( 25, 25, 112 ) );
        put( "mintcream", new Color( 245, 255, 250 ) );
        put( "mistyrose", new Color( 255, 228, 225 ) );
        put( "moccasin", new Color( 255, 228, 181 ) );
        put( "navajowhite", new Color( 255, 222, 173 ) );
        put( "oldlace", new Color( 253, 245, 230 ) );
        put( "olivedrab", new Color( 107, 142, 35 ) );
        put( "orangered", new Color( 255, 69, 0 ) );
        put( "orchid", new Color( 218, 112, 214 ) );
        put( "palegoldenrod", new Color( 238, 232, 170 ) );
        put( "palegreen", new Color( 152, 251, 152 ) );
        put( "paleturquoise", new Color( 175, 238, 238 ) );
        put( "palevioletred", new Color( 219, 112, 147 ) );
        put( "papayawhip", new Color( 255, 239, 213 ) );
        put( "peachpuff", new Color( 255, 218, 185 ) );
        put( "peru", new Color( 205, 133, 63 ) );
        put( "pink", new Color( 255, 192, 203 ) );
        put( "plum", new Color( 221, 160, 221 ) );
        put( "powderblue", new Color( 176, 224, 230 ) );
        put( "rosybrown", new Color( 188, 143, 143 ) );
        put( "royalblue", new Color( 65, 105, 225 ) );
        put( "saddlebrown", new Color( 139, 69, 19 ) );
        put( "salmon", new Color( 250, 128, 114 ) );
        put( "sandybrown", new Color( 244, 164, 96 ) );
        put( "seagreen", new Color( 46, 139, 87 ) );
        put( "seashell", new Color( 255, 245, 238 ) );
        put( "sienna", new Color( 160, 82, 45 ) );
        put( "skyblue", new Color( 135, 206, 235 ) );
        put( "slateblue", new Color( 106, 90, 205 ) );
        put( "slategray", new Color( 112, 128, 144 ) );
        put( "slategrey", new Color( 112, 128, 144 ) );
        put( "snow", new Color( 255, 250, 250 ) );
        put( "springgreen", new Color( 0, 255, 127 ) );
        put( "steelblue", new Color( 70, 130, 180 ) );
        put( "tan", new Color( 210, 180, 140 ) );
        put( "thistle", new Color( 216, 191, 216 ) );
        put( "tomato", new Color( 255, 99, 71 ) );
        put( "turquoise", new Color( 64, 224, 208 ) );
        put( "violet", new Color( 238, 130, 238 ) );
        put( "wheat", new Color( 245, 222, 179 ) );
        put( "whitesmoke", new Color( 245, 245, 245 ) );
        put( "yellowgreen", new Color( 154, 205, 50 ) );
        }

    /**
     * Gets the color value from percentage.
     *
     * For example:
     * 100% -> 255
     * 50%  -> 128
     * 0%   -> 0
     *
     * @param aPercentage the a percentage
     *
     * @return the color value from percentage
     */
    public int getColorValueFromPercentage( float aPercentage )
        {
        if ( aPercentage < 0 || PERCENTAGE_MAX_VALUE < aPercentage )
            {
            throw new IllegalStateException( "Color percentage out of range" );
            }
        float value = RGB_MAX_VALUE * ( ( aPercentage ) / PERCENTAGE_MAX_VALUE );
        return ( int ) ( value + 0.5f );
        }

    /**
     * Translate color from HSL to RGB.
     *
     * The algorithm is taken from
     * CSS3 Color Module:
     * http://www.w3.org/TR/css3-color/:
     *
     * @param aHue Hue
     * @param aSaturation Saturation
     * @param aLightness Lightness
     *
     * @return the color
     */
    public Color hslToRgb( float aHue, float aSaturation, float aLightness )
        {

        /*
          In these algorithms, all
          three values (H, S and L) have been normalized to fractions 0..1:

              HOW TO RETURN hsl.to.rgb(h, s, l):
              SELECT:
              l<=0.5: PUT l*(s+1) IN m2
              ELSE: PUT l+s-l*s IN m2
               PUT l*2-m2 IN m1
               PUT hue.to.rgb(m1, m2, h+1/3) IN r
               PUT hue.to.rgb(m1, m2, h    ) IN g
               PUT hue.to.rgb(m1, m2, h-1/3) IN b
               RETURN (r, g, b)

              HOW TO RETURN hue.to.rgb(m1, m2, h):
               IF h<0: PUT h+1 IN h
               IF h>1: PUT h-1 IN h
               IF h*6<1: RETURN m1+(m2-m1)*h*6
               IF h*2<1: RETURN m2
               IF h*3<2: RETURN m1+(m2-m1)*(2/3-h)*6
               RETURN m1


         */

        float h = aHue;
        h /= 360;

        if ( aSaturation < 0 || 100 < aSaturation
                || aLightness < 0 || 100 < aLightness )
            {
            throw new IllegalStateException( "HSL value out of range" );
            }

        float s = aSaturation;
        s /= 100;

        float l = aLightness;
        l /= 100;

        float[] color = { 0, 0, 0 };

        // If Saturation is zero, return gray with correct lightness
        if ( aSaturation == 0 )
            {
            int e = ( int ) ( RGB_MAX_VALUE * l + 0.5f );
            return new Color( e, e, e );
            }

        // HOW TO RETURN hsl.to.rgb(h, s, l):
        // SELECT:
        // l<=0.5: PUT l*(s+1) IN m2
        // ELSE: PUT l+s-l*s IN m2
        float m2 = 0;

        if ( l < 0.5 )
            {
            m2 = l * ( 1.0f + s );
            }

        if ( l >= 0.5 )
            {
            m2 = l + s - l * s;
            }

        // temp1 = 2.0*L - temp2
        // PUT l*2-m2 IN m1
        float m1 = 2.0f * l - m2;

        // PUT hue.to.rgb(m1, m2, h+1/3) IN r
        // PUT hue.to.rgb(m1, m2, h ) IN g
        // PUT hue.to.rgb(m1, m2, h-1/3) IN b
        float tempRGB[] = { h + 1.0f / 3.0f, h, h - 1.0f / 3.0f };

        for ( int i = 0; i < 3; i++ )
            {
            // HOW TO RETURN hue.to.rgb(m1, m2, h):
            // IF h<0: PUT h+1 IN h
            if ( tempRGB[ i ] < 0 )
                {
                tempRGB[ i ] = tempRGB[ i ] + 1.0f;
                }
            // IF h>1: PUT h-1 IN h
            if ( tempRGB[ i ] > 1 )
                {
                tempRGB[ i ] = tempRGB[ i ] - 1.0f;
                }

            // HOW TO RETURN hue.to.rgb(m1, m2, h):
            // IF h*6<1: RETURN m1+(m2-m1)*h*6
            if ( 6.0f * tempRGB[ i ] < 1.0f )
                {
                color[ i ] = m1 + ( m2 - m1 ) * 6.0f * tempRGB[ i ];
                }
            // HOW TO RETURN hue.to.rgb(m1, m2, h):
            // IF h*2<1: RETURN m2
            else if ( 2.0f * tempRGB[ i ] < 1.0f )
                {
                color[ i ] = m2;
                }
            // HOW TO RETURN hue.to.rgb(m1, m2, h):
            // IF h*3<2: RETURN m1+(m2-m1)*(2/3-h)*6
            else if ( 3.0f * tempRGB[ i ] < 2.0f )
                {
                color[ i ] = m1 + ( m2 - m1 )
                        * ( ( 2.0f / 3.0f ) - tempRGB[ i ] ) * 6.0f;
                }
            // HOW TO RETURN hue.to.rgb(m1, m2, h):
            // ELSE RETURN m1
            else
                {
                color[ i ] = m1;
                }
            }

        // Scale color back from [0..1] to [0..255]
        return new Color( ( int ) ( 255f * color[ 0 ] + 0.5f ),
                ( int ) ( 255f * color[ 1 ] + 0.5f ),
                ( int ) ( 255f * color[ 2 ] + 0.5f ) );
        }

    }
