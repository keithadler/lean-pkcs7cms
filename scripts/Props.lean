import CMS.Widget

/-! Writes `docs/props.json`, the data the widget page draws: `lake env lean scripts/Props.lean`. -/

#eval IO.FS.writeFile "docs/props.json" CMS.Widget.widgetProps.pretty
