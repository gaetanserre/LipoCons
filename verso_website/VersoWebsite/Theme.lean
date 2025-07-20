/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoBlog
import VersoWebsite.Front
import VersoWebsite.Constant


open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }}</title>
          <link rel="icon" type="image/x-icon" href="/static/favicon.svg"/>
          <script src="/static/scripts.js"/>
          {{← builtinHeader }}
        </head>
        <body>
          <div class="title">
            <a href="/">{{website_title}}</a>
          </div>
          <div class="row">
            <div class="column_outline">
              <div class="toc">{{" Table of contents"}}</div>
              <div class="inner-wrap">
              {{ ← topNav }}
              </div>
            </div>
            <div class="column_content">
              <div class="main" role="main">
                <div class="wrap">
                  {{ (← param "content") }}
                </div>
              </div>
            </div>
          </div>
        </body>
        <link rel="stylesheet" href="/static/style.css"/>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩
