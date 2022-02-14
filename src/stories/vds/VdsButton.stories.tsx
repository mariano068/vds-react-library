import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { primary_contained_button_example_snippet, Primary_Contained_Button_Example_Snippet, primary_outlined_button_example_snippet, Primary_Outlined_Button_Example_Snippet, secondary_contained_button_example_snippet, Secondary_Contained_Button_Example_Snippet } from '../snippets/VdsButton.snippets';

const storyTitle = 'Button';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>Buttons are meant to express actions in page. Also called Calls To Action (CTA) they are the tool used to define the interaction space target to click -or touch- to trigger behaviors.</p>
      <h3>Standard Buttons</h3>
      <h4>Primary Blue</h4>
      <p>
        The primary button blue is always used to highlight the main positive action in page on light background. All the other buttons will be secondary blue or tertiary blue in the page.
      </p>
      <CodeHighlight>
        <Primary_Contained_Button_Example_Snippet />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{primary_contained_button_example_snippet}</Highlight>
      <h3>Secondary Blue</h3>
      <p>
        The secondary button blue is always used to express all the secondary positive actions in page on light background. The main action in page will be primary blue and the less important one tertiary blue.
      </p>
      <CodeHighlight>
        <Primary_Outlined_Button_Example_Snippet />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{primary_outlined_button_example_snippet}</Highlight>
      <h3>Alert buttons</h3>
      <p>
        We have designed custom buttons to be used to unform users of potentially dangerous actions they're about to take. If used within a set, the alert button should be styled as a primary button. Alert button is used for actions that require specific attention or a possible harming consequence (ie: delete, cancel, reject ...)
      </p>
      <CodeHighlight>
        <Secondary_Contained_Button_Example_Snippet />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{secondary_contained_button_example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
