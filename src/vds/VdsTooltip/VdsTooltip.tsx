import { styled, Tooltip } from "@mui/material";
import * as React from 'react';

export const VdsTooltip = styled(({ className, ...props }: any) => <Tooltip
    {...props}
    componentsProps={{ tooltip: { className } }}
/>)({
    backgroundColor: "#005075",
    fontSize: "12px",
    color: "#FFFFFF",
    letterSpacing: "0",
    textAlign: "center",
    lineHeight: "12px",
    fontFamily: "Roboto",
    fontWeight: 500,
    borderRadius: "2px",
    padding: "6px 8px",
    'span': {
        color: "#005075",
    }
});
